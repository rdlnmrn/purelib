module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.DropWhile.Basic
import Purelib.Data.Rat.Bounds.Square
import Purelib.Polynomial.Power.Gaussian.Squarefree
public import Purelib.RootIsolation.Power.Clearance.Box.Transport
import Purelib.Algebra.Field.ExplicitField
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Cast.Imaginary
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Bounds
import Purelib.Geometry.Rational.Box.Dimensions
import Purelib.Geometry.Rational.Box.Intervals
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Lines
import Purelib.Polynomial.Clearance.Box.Grid.Four.Basic
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Clearance.Box.Line.Restriction
import Purelib.Polynomial.Clearance.Box.ProtectedRadius
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Path.Majorant
import Purelib.Polynomial.Dense.Gaussian.Components
import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Polynomial.Dense.Gaussian.Substitution.Affine
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Rational.Bounds.Horner
import Purelib.Polynomial.Power.Gaussian
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.RootIsolation.Newton.Search.Attempt
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Subdivision.Raw.Request
import Purelib.RootIsolation.Track.Basic
import Purelib.RootIsolation.Track.Newton.Refinement

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.RootContinuation.SquareRootContinuation
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticAxisElimination
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance
public import Purelib.Riemann.Topology.SquareRootContinuationChain
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Clearance.Box.Grid.Four.Clearance
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.Refinement.Basic
import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data.Rat.Interval.Bounds (Refines)
open Purelib.Polynomial.Clearance.Box.Boundary.Basic (BoundaryClearance)
open Purelib.Polynomial.Clearance.Box.Line.Basic (HorizontalLineClearance VerticalLineClearance)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.RootIsolation.State.WindingOne.Basic (WindingOneState)

open Purelib

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

public section

/-!
# Exact boundary clearance for a displayed quadratic owner

For an owner of `Z² - parameter`, the four side-resultant determinants are
explicit rational expressions.  When all four are nonzero, this module
repackages the existing winding-one box with the exact resultant clearances.
If any check fails, it returns the original owner.  The operation is therefore
total, constructive, executable, and never weakens the inherited clearance.
-/

namespace Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance

open Fraction.Order
open Purelib.Data.List

open Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance
open Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance
  renaming Box -> QuadraticBox
open Purelib.RootIsolation.SquareRoot.Clearance

/-- Dense polynomials over the original rational coordinate field. -/
abbrev Polynomial := DensePolynomial Coordinate
/-- The original square-root continuation owner, retaining its nonzero parameter, ambient box and winding track. -/
abbrev Owner := Riemann.Topology.SquareRootContinuationChain.Owner

/-- The boundary-clearance bound of an owner is no larger than any of its
four ambient-line bounds.  This finite invariant lets one displacement check
justify all five constant-term transports. -/
structure AmbientClearanceDominance {parameter : Gaussian}
    (owner : Owner parameter) : Prop where
  /-- The original boundary bound is no larger than the retained left ambient-line bound. -/ left :
    owner.track.initial.clearance.bound <=
    owner.track.initial.ambientLeftClearance.bound
  /-- The original boundary bound is no larger than the retained right ambient-line bound. -/ right :
    owner.track.initial.clearance.bound <=
    owner.track.initial.ambientRightClearance.bound
  /-- The original boundary bound is no larger than the retained bottom ambient-line bound. -/ bottom :
    owner.track.initial.clearance.bound <=
    owner.track.initial.ambientBottomClearance.bound
  /-- The original boundary bound is no larger than the retained top ambient-line bound. -/ top :
    owner.track.initial.clearance.bound <=
    owner.track.initial.ambientTopClearance.bound

namespace AmbientClearanceDominance

/-- A move smaller than the boundary clearance is automatically smaller than
all four ambient-line clearances when the owner carries the dominance
invariant. -/
theorem ambientSmallness {source target : Gaussian} {owner : ExactQuadraticOwnerClearance.Owner source}
    (dominance : ExactQuadraticOwnerClearance.AmbientClearanceDominance owner)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.clearance.bound) :
    Data.Gaussian.Norm.Basic.normSq (source - target) <
        owner.track.initial.ambientLeftClearance.bound /\
      Data.Gaussian.Norm.Basic.normSq (source - target) <
          owner.track.initial.ambientRightClearance.bound /\
        Data.Gaussian.Norm.Basic.normSq (source - target) <
            owner.track.initial.ambientBottomClearance.bound /\
          Data.Gaussian.Norm.Basic.normSq (source - target) <
            owner.track.initial.ambientTopClearance.bound :=
  ⟨small.trans_le dominance.left, small.trans_le dominance.right,
    small.trans_le dominance.bottom, small.trans_le dominance.top⟩

end AmbientClearanceDominance

/-- The original quadratic polynomial Z² minus the displayed Gaussian parameter. -/
@[expose] def rootPolynomial (parameter : Gaussian) : GaussianPolynomial :=
  Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
    Riemann.RootContinuation.SquareRootDegree.degreeTwo

section QuadraticPathCoefficients

open Purelib.Polynomial.Dense.Basic.DensePolynomial

/-- Adding a constant to a quadratic with nonzero leading coefficient changes only its retained constant coefficient.

The original nonzero leading Gaussian coefficient survives the same finite leading-zero scan; the constant aligns with
the retained trailing coefficient. -/
private theorem quadratic_add_constant
    {leading : Gaussian} (middle trailing constantTerm : Gaussian)
    (leadingNonzero : leading ≠ 0) :
    (⟨[leading, middle, trailing]⟩ : GaussianPolynomial) +
        DensePolynomial.constant constantTerm =
      ⟨[leading, middle, trailing + constantTerm]⟩ := by
  apply DensePolynomial.ext
  change [leading + 0, middle + 0, trailing + constantTerm].dropWhile
      (fun value => decide (value = 0)) = [leading, middle, trailing + constantTerm]
  rw [Gaussian.Basic.add_zero, Gaussian.Basic.add_zero]
  exact DropWhile.cons_of_false (fun value => decide (value = 0))
    leading [middle, trailing + constantTerm] (decide_eq_false leadingNonzero)

/-- The exact three coefficients obtained by multiplying a retained linear polynomial by a nondegenerate affine line.

The original nonzero origin, direction and leading coefficient retain both scaled linear tables. The same one-place
shift and aligned sum supply the exact three output coefficients. -/
private theorem mulLine_two_coeffs
    (origin direction a b : Gaussian)
    (originNonzero : origin ≠ 0) (directionNonzero : direction ≠ 0)
    (leadingNonzero : a ≠ 0) (polynomial : GaussianPolynomial)
    (coefficients : polynomial.coeffs = [a, b]) :
    (Purelib.Polynomial.Dense.Gaussian.Substitution.Affine.mulLine origin direction polynomial).coeffs =
      [direction * a, direction * b + origin * a, origin * b] := by
  unfold Dense.Gaussian.Substitution.Affine.mulLine
  have normalized : polynomial.normalize.coeffs = [a, b] := by
    rw [DensePolynomial.normalize_coeffs, coefficients]
    exact DropWhile.cons_of_false (fun value => decide (value = 0))
      a [b] (decide_eq_false leadingNonzero)
  let originScaled : GaussianPolynomial := ⟨[origin * a, origin * b]⟩
  let directionScaled : GaussianPolynomial := ⟨[direction * a, direction * b]⟩
  have originScaleEq : DensePolynomial.scale origin polynomial = originScaled := by
    apply DensePolynomial.ext
    rw [DensePolynomial.scale_coeffs_of_ne_zero originNonzero, normalized]
    rfl
  have directionScaleEq : DensePolynomial.scale direction polynomial = directionScaled := by
    apply DensePolynomial.ext
    rw [DensePolynomial.scale_coeffs_of_ne_zero directionNonzero, normalized]
    rfl
  rw [originScaleEq, directionScaleEq]
  have leadingProductNonzero : direction * a ≠ 0 :=
    Gaussian.Field.mul_ne_zero_direct directionNonzero leadingNonzero
  have directionScaledNormalized : directionScaled.normalize = directionScaled :=
    DensePolynomial.normalize_linear_of_leading_ne_zero leadingProductNonzero
  have directionScaledNotZero : directionScaled.isZero = false := by
    change directionScaled.normalize.coeffs.isEmpty = false
    rw [directionScaledNormalized]
    rfl
  have shifted : DensePolynomial.shift 1 directionScaled =
      ⟨[direction * a, direction * b, 0]⟩ := by
    unfold DensePolynomial.shift
    rw [if_neg]
    · rw [directionScaledNormalized]
      rfl
    · intro empty
      change directionScaled.isZero = true at empty
      have impossible : false = true := directionScaledNotZero.symm.trans empty
      cases impossible
  rw [shifted]
  change [0 + direction * a, origin * a + direction * b, origin * b + 0].dropWhile
      (fun value => decide (value = 0)) = _
  rw [Gaussian.Basic.zero_add, Gaussian.Basic.add_zero,
    DropWhile.cons_of_false (fun value => decide (value = 0))
      (direction * a) [origin * a + direction * b, origin * b]
      (decide_eq_false leadingProductNonzero)]
  exact congrArg (fun middle : Gaussian => [direction * a, middle, origin * b])
    (Gaussian.Basic.add_comm _ _)

/-- The exact three Gaussian coefficients of Z² minus the parameter after nondegenerate affine substitution.

The same original Horner recursion through the retained quadratic table gives the displayed Gaussian coefficients; the
nonzero origin and direction preserve its intermediate linear normalization. -/
private theorem composeLine_quadratic
    (parameter origin direction : Gaussian)
    (originNonzero : origin ≠ 0) (directionNonzero : direction ≠ 0) :
    Purelib.Polynomial.Dense.Gaussian.Substitution.Affine.composeLine
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        origin direction =
      ⟨[direction * direction,
        direction * origin + origin * direction,
        origin * origin - parameter]⟩ := by
  unfold Dense.Gaussian.Substitution.Affine.composeLine
    Dense.Gaussian.Substitution.Affine.composeLineCoeffs
    Power.Gaussian.rootPolynomial
    Riemann.RootContinuation.SquareRootDegree.degreeTwo
  simp only [List.replicate_succ, List.replicate_zero, List.nil_append,
    List.cons_append, List.foldl_cons, List.foldl_nil]
  rw [Dense.Gaussian.Substitution.Affine.mulLine_zero, DensePolynomial.zero_add_normalize,
    DensePolynomial.normalize_constant_of_ne one_ne_zero]
  have first : Dense.Gaussian.Substitution.Affine.mulLine origin direction (DensePolynomial.constant 1) =
      (⟨[direction, origin]⟩ : GaussianPolynomial) := by
    rw [Dense.Gaussian.Substitution.Affine.mulLine, DensePolynomial.scale_constant,
      DensePolynomial.scale_constant,
      Gaussian.Basic.mul_one,
      Gaussian.Basic.mul_one,
      DensePolynomial.normalize_constant_of_ne directionNonzero,
      DensePolynomial.shift_one_constant_of_ne directionNonzero,
      DensePolynomial.normalize_constant_of_ne originNonzero,
      DensePolynomial.constant_add_linear origin directionNonzero]
  have linearNormalized :
      (⟨[direction, origin]⟩ : GaussianPolynomial).normalize =
        ⟨[direction, origin]⟩ := by
    exact DensePolynomial.normalize_linear_of_leading_ne_zero directionNonzero
  rw [first, DensePolynomial.add_constant_zero, linearNormalized]
  have secondMul :
      Dense.Gaussian.Substitution.Affine.mulLine origin direction
          (⟨[direction, origin]⟩ : GaussianPolynomial) =
        ⟨[direction * direction, direction * origin + origin * direction,
          origin * origin]⟩ := by
    apply DensePolynomial.ext
    exact mulLine_two_coeffs origin direction direction origin
      originNonzero directionNonzero directionNonzero
        ⟨[direction, origin]⟩ rfl
  rw [secondMul, quadratic_add_constant
    (direction * origin + origin * direction) (origin * origin)
      (-parameter)
      (Gaussian.Field.mul_ne_zero_direct
        directionNonzero directionNonzero)]
  rw [Gaussian.Basic.sub_eq_add_neg]

/-- The quadratic affine cache at the zero origin.  This is separate from
the nonzero-origin cache because the intermediate Horner polynomial
normalizes to a shorter coefficient list.

The original zero-origin scale and retained nonzero squared direction fix the selected shift branch, preserving the
exact original three-coefficient table. -/
private theorem composeLine_quadratic_zero
    (parameter direction : Gaussian) (directionNonzero : direction ≠ 0) :
    Purelib.Polynomial.Dense.Gaussian.Substitution.Affine.composeLine
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        0 direction =
      ⟨[direction * direction, 0, -parameter]⟩ := by
  have first : Dense.Gaussian.Substitution.Affine.mulLine 0 direction (DensePolynomial.constant 1) =
      (⟨[direction, 0]⟩ : GaussianPolynomial) := by
    unfold Dense.Gaussian.Substitution.Affine.mulLine
    rw [DensePolynomial.scale_zero_left, DensePolynomial.scale_constant,
      Gaussian.Basic.mul_one,
      DensePolynomial.normalize_constant_of_ne directionNonzero,
      DensePolynomial.shift_one_constant_of_ne directionNonzero,
        DensePolynomial.zero_add_normalize,
      ]
    exact DensePolynomial.normalize_linear_of_leading_ne_zero directionNonzero
  have firstNormalized :
      (⟨[direction, 0]⟩ : GaussianPolynomial).normalize =
        ⟨[direction, 0]⟩ := by
    exact DensePolynomial.normalize_linear_of_leading_ne_zero directionNonzero
  have directionSqNonzero : direction * direction ≠ 0 :=
    Gaussian.Field.mul_ne_zero_direct directionNonzero
      directionNonzero
  have directionScaled : DensePolynomial.scale direction
      (⟨[direction, 0]⟩ : GaussianPolynomial) =
        ⟨[direction * direction, 0]⟩ := by
    apply DensePolynomial.ext
    rw [DensePolynomial.scale_coeffs_of_ne_zero directionNonzero,
      congrArg DensePolynomial.coeffs
        firstNormalized]
    rw [List.map_cons, List.map_cons, List.map_nil, Gaussian.Basic.mul_zero]
  have second : Dense.Gaussian.Substitution.Affine.mulLine 0 direction
      (⟨[direction, 0]⟩ : GaussianPolynomial) =
        ⟨[direction * direction, 0, 0]⟩ := by
    unfold Dense.Gaussian.Substitution.Affine.mulLine
    rw [DensePolynomial.scale_zero_left, directionScaled, DensePolynomial.zero_add_normalize,
      DensePolynomial.normalize_shift]
    have normalized :
        (⟨[direction * direction, 0]⟩ : GaussianPolynomial).normalize =
          ⟨[direction * direction, 0]⟩ :=
      DensePolynomial.normalize_linear_of_leading_ne_zero directionSqNonzero
    have notZero : (⟨[direction * direction, 0]⟩ : GaussianPolynomial).isZero = false := by
      change (⟨[direction * direction, 0]⟩ : GaussianPolynomial).normalize.coeffs.isEmpty = false
      rw [normalized]
      rfl
    unfold DensePolynomial.shift
    rw [if_neg]
    · rw [normalized]
      rfl
    · intro empty
      change (⟨[direction * direction, 0]⟩ : GaussianPolynomial).isZero = true at empty
      have impossible : false = true := notZero.symm.trans empty
      cases impossible
  unfold Dense.Gaussian.Substitution.Affine.composeLine
    Dense.Gaussian.Substitution.Affine.composeLineCoeffs
    Power.Gaussian.rootPolynomial
    Riemann.RootContinuation.SquareRootDegree.degreeTwo
  simp only [List.replicate_succ, List.replicate_zero, List.nil_append,
    List.cons_append, List.foldl_cons, List.foldl_nil]
  rw [Dense.Gaussian.Substitution.Affine.mulLine_zero, DensePolynomial.zero_add_normalize,
    DensePolynomial.normalize_constant_of_ne one_ne_zero, first,
      DensePolynomial.add_constant_zero,
    firstNormalized, second,
    quadratic_add_constant 0 0 (-parameter) directionSqNonzero]
  rw [Gaussian.Basic.zero_add]

/-- Exact three real coefficients of `Z²-parameter` on a nonzero vertical
line.  This is the compact Horner cache used by explicit transport bounds. -/
theorem quadraticVerticalPathReal (parameter : Gaussian) (x : Coordinate)
    (xNonzero : x ≠ 0) :
    Dense.Gaussian.Path.Components.pathReal
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit =
      (⟨[-1, 0, x ^ 2 - parameter.re]⟩ : Polynomial) := by
  unfold Dense.Gaussian.Path.Components.pathReal
  rw [composeLine_quadratic]
  · apply DensePolynomial.ext
    simp only [Dense.Gaussian.Components.realPart, List.map_cons, List.map_nil,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.add_re,
      Gaussian.Basic.sub_re,
      Gaussian.Cast.Winding.verticalBase, Gaussian.Constants.imaginaryUnit]
    congr 3 <;> ring1
  · intro zero
    have real := congrArg (fun value : Gaussian => value.re) zero
    exact xNonzero real
  · intro zero
    have imaginary := congrArg (fun value : Gaussian => value.im) zero
    exact (by decide : (1 : Coordinate) ≠ 0) imaginary

/-- Exact three imaginary coefficients of `Z²-parameter` on a nonzero
vertical line. -/
theorem quadraticVerticalPathImag (parameter : Gaussian) (x : Coordinate)
    (xNonzero : x ≠ 0) :
    Dense.Gaussian.Path.Components.pathImag
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit =
      (⟨[0, 2 * x, -parameter.im]⟩ : Polynomial) := by
  unfold Dense.Gaussian.Path.Components.pathImag
  rw [composeLine_quadratic]
  · apply DensePolynomial.ext
    simp only [Dense.Gaussian.Components.imagPart, List.map_cons, List.map_nil,
      Gaussian.Basic.mul_im,
      Gaussian.Basic.add_im,
      Gaussian.Basic.sub_im,
      Gaussian.Cast.Winding.verticalBase, Gaussian.Constants.imaginaryUnit]
    congr 3 <;> ring1
  · intro zero
    have real := congrArg (fun value : Gaussian => value.re) zero
    exact xNonzero real
  · intro zero
    have imaginary := congrArg (fun value : Gaussian => value.im) zero
    exact (by decide : (1 : Coordinate) ≠ 0) imaginary

/-- Exact real coefficients on the vertical axis. -/
theorem quadraticVerticalPathReal_zero (parameter : Gaussian) :
    Dense.Gaussian.Path.Components.pathReal
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Winding.verticalBase 0) Gaussian.Constants.imaginaryUnit =
      (⟨[-1, 0, -parameter.re]⟩ : Polynomial) := by
  unfold Dense.Gaussian.Path.Components.pathReal
  rw [show Gaussian.Cast.Winding.verticalBase 0 = (0 : Gaussian) by rfl,
    composeLine_quadratic_zero parameter Gaussian.Constants.imaginaryUnit
      (by decide)]
  apply DensePolynomial.ext
  simp only [Dense.Gaussian.Components.realPart, List.map_cons, List.map_nil,
    Gaussian.Basic.mul_re,
    Gaussian.Basic.neg_re,
    Gaussian.Constants.imaginaryUnit]
  rfl

/-- Exact imaginary coefficients on the vertical axis. -/
theorem quadraticVerticalPathImag_zero (parameter : Gaussian) :
    Dense.Gaussian.Path.Components.pathImag
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Winding.verticalBase 0) Gaussian.Constants.imaginaryUnit =
      (⟨[0, 0, -parameter.im]⟩ : Polynomial) := by
  unfold Dense.Gaussian.Path.Components.pathImag
  rw [show Gaussian.Cast.Winding.verticalBase 0 = (0 : Gaussian) by rfl,
    composeLine_quadratic_zero parameter Gaussian.Constants.imaginaryUnit
      (by decide)]
  apply DensePolynomial.ext
  simp only [Dense.Gaussian.Components.imagPart, List.map_cons, List.map_nil,
    Gaussian.Basic.mul_im,
    Gaussian.Basic.neg_im,
    Gaussian.Constants.imaginaryUnit]
  rfl

/-- Exact vertical real coefficients, including the normalized axis case. -/
theorem quadraticVerticalPathReal_all (parameter : Gaussian) (x : Coordinate) :
    Dense.Gaussian.Path.Components.pathReal
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit =
      (⟨[-1, 0, x ^ 2 - parameter.re]⟩ : Polynomial) := by
  by_cases xZero : x = 0
  · rw [xZero]
    simpa only [zero_pow (by decide : 2 ≠ 0), zero_sub] using
      quadraticVerticalPathReal_zero parameter
  · exact quadraticVerticalPathReal parameter x xZero

/-- Exact vertical imaginary coefficients, including the normalized axis
case. -/
theorem quadraticVerticalPathImag_all (parameter : Gaussian) (x : Coordinate) :
    Dense.Gaussian.Path.Components.pathImag
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit =
      (⟨[0, 2 * x, -parameter.im]⟩ : Polynomial) := by
  by_cases xZero : x = 0
  · rw [xZero]
    simpa only [Fraction.Field.mul_zero_direct] using
      quadraticVerticalPathImag_zero parameter
  · exact quadraticVerticalPathImag parameter x xZero

/-- Exact three real coefficients of `Z²-parameter` on a nonzero horizontal
line. -/
theorem quadraticHorizontalPathReal (parameter : Gaussian) (y : Coordinate)
    (yNonzero : y ≠ 0) :
    Dense.Gaussian.Path.Components.pathReal
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Imaginary.horizontalBase y) Gaussian.Constants.horizontalDirection =
      (⟨[1, 0, -(y ^ 2) - parameter.re]⟩ : Polynomial) := by
  unfold Dense.Gaussian.Path.Components.pathReal
  rw [composeLine_quadratic]
  · apply DensePolynomial.ext
    simp only [Dense.Gaussian.Components.realPart, List.map_cons, List.map_nil,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.add_re,
      Gaussian.Basic.sub_re,
      Gaussian.Cast.Imaginary.horizontalBase, Gaussian.Constants.horizontalDirection]
    congr 3 <;> ring1
  · intro zero
    have imaginary := congrArg (fun value : Gaussian => value.im) zero
    exact yNonzero imaginary
  · intro zero
    have real := congrArg (fun value : Gaussian => value.re) zero
    exact (by decide : (1 : Coordinate) ≠ 0) real

/-- Exact real coefficients on the horizontal axis. -/
theorem quadraticHorizontalPathReal_zero (parameter : Gaussian) :
    Dense.Gaussian.Path.Components.pathReal
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Imaginary.horizontalBase 0) Gaussian.Constants.horizontalDirection =
      (⟨[1, 0, -parameter.re]⟩ : Polynomial) := by
  unfold Dense.Gaussian.Path.Components.pathReal
  rw [show Gaussian.Cast.Imaginary.horizontalBase 0 = (0 : Gaussian) by rfl,
    composeLine_quadratic_zero parameter
      Gaussian.Constants.horizontalDirection (by decide)]
  apply DensePolynomial.ext
  simp only [Dense.Gaussian.Components.realPart, List.map_cons, List.map_nil,
    Gaussian.Basic.mul_re,
    Gaussian.Basic.neg_re,
    Gaussian.Constants.horizontalDirection]
  rfl

/-- Exact three imaginary coefficients of `Z²-parameter` on a nonzero
horizontal line. -/
theorem quadraticHorizontalPathImag (parameter : Gaussian) (y : Coordinate)
    (yNonzero : y ≠ 0) :
    Dense.Gaussian.Path.Components.pathImag
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Imaginary.horizontalBase y) Gaussian.Constants.horizontalDirection =
      (⟨[0, 2 * y, -parameter.im]⟩ : Polynomial) := by
  unfold Dense.Gaussian.Path.Components.pathImag
  rw [composeLine_quadratic]
  · apply DensePolynomial.ext
    simp only [Dense.Gaussian.Components.imagPart, List.map_cons, List.map_nil,
      Gaussian.Basic.mul_im,
      Gaussian.Basic.add_im,
      Gaussian.Basic.sub_im,
      Gaussian.Cast.Imaginary.horizontalBase, Gaussian.Constants.horizontalDirection]
    congr 3 <;> ring1
  · intro zero
    have imaginary := congrArg (fun value : Gaussian => value.im) zero
    exact yNonzero imaginary
  · intro zero
    have real := congrArg (fun value : Gaussian => value.re) zero
    exact (by decide : (1 : Coordinate) ≠ 0) real

/-- Exact imaginary coefficients on the horizontal axis. -/
theorem quadraticHorizontalPathImag_zero (parameter : Gaussian) :
    Dense.Gaussian.Path.Components.pathImag
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Imaginary.horizontalBase 0) Gaussian.Constants.horizontalDirection =
      (⟨[0, 0, -parameter.im]⟩ : Polynomial) := by
  unfold Dense.Gaussian.Path.Components.pathImag
  rw [show Gaussian.Cast.Imaginary.horizontalBase 0 = (0 : Gaussian) by rfl,
    composeLine_quadratic_zero parameter
      Gaussian.Constants.horizontalDirection (by decide)]
  apply DensePolynomial.ext
  simp only [Dense.Gaussian.Components.imagPart, List.map_cons, List.map_nil,
    Gaussian.Basic.mul_im,
    Gaussian.Basic.neg_im,
    Gaussian.Constants.horizontalDirection]
  rfl

/-- Exact horizontal real coefficients, including the normalized axis case. -/
theorem quadraticHorizontalPathReal_all (parameter : Gaussian)
    (y : Coordinate) :
    Dense.Gaussian.Path.Components.pathReal
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Imaginary.horizontalBase y) Gaussian.Constants.horizontalDirection =
      (⟨[1, 0, -(y ^ 2) - parameter.re]⟩ : Polynomial) := by
  by_cases yZero : y = 0
  · subst y
    simpa only [zero_pow (by decide : 2 ≠ 0), neg_zero, sub_eq_add_neg,
      zero_add] using quadraticHorizontalPathReal_zero parameter
  · exact quadraticHorizontalPathReal parameter y yZero

/-- Exact horizontal imaginary coefficients, including the normalized axis
case. -/
theorem quadraticHorizontalPathImag_all (parameter : Gaussian)
    (y : Coordinate) :
    Dense.Gaussian.Path.Components.pathImag
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Imaginary.horizontalBase y) Gaussian.Constants.horizontalDirection =
      (⟨[0, 2 * y, -parameter.im]⟩ : Polynomial) := by
  by_cases yZero : y = 0
  · rw [yZero]
    simpa only [Fraction.Field.mul_zero_direct] using
      quadraticHorizontalPathImag_zero parameter
  · exact quadraticHorizontalPathImag parameter y yZero

end QuadraticPathCoefficients

/-- The finite Horner square bound of a three-coefficient polynomial is at most 8192 under the displayed coefficient and
interval bounds. -/
private theorem threeCoefficientHorner_le
    (polynomial : Polynomial) (a b c : Coordinate)
    (coefficients : polynomial.coeffs = [a, b, c])
    (interval : Data.Rat.Interval.Bounds)
    (radiusLe : interval.squareBound ≤ 16)
    (aSqLe : a ^ 2 ≤ 1) (bSqLe : b ^ 2 ≤ 64)
    (cSqLe : c ^ 2 ≤ 1024) :
    Purelib.Polynomial.Dense.Rational.Bounds.Horner.evalSqBound polynomial interval ≤ 8192 := by
  calc
    Dense.Rational.Bounds.Horner.evalSqBound polynomial interval ≤
        2 * ((2 * ((2 * (1 : Coordinate)) * 16 + 64)) * 16 + 1024) :=
      Dense.Rational.Bounds.Horner.evalSqBound_three_le polynomial a b c coefficients
        interval 16 1 64 1024
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 16) (by decide)).le
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 1) (by decide)).le
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 64) (by decide)).le
        radiusLe aSqLe bSqLe cSqLe
    _ = 8192 := by ring1

/-- The squared sum of a bounded coordinate square and bounded component is at most 1024.

The two original coordinate-square bounds control the squared coordinate sum through the same rational sum-of-squares
inequality. -/
private theorem coordinateSquare_add_component_sq_le
    (coordinate component : Coordinate)
    (coordinateSqLe : coordinate ^ 2 ≤ 16)
    (componentSqLe : component ^ 2 ≤ 256) :
    (coordinate ^ 2 + component) ^ 2 ≤ 1024 := by
  have coordinateFourthLe : (coordinate ^ 2) ^ 2 ≤ (16 : Coordinate) ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct
      (Fraction.Order.Arithmetic.sq_nonneg_direct coordinate)
      coordinateSqLe 2
  calc
    (coordinate ^ 2 + component) ^ 2 ≤
        2 * ((coordinate ^ 2) ^ 2 + component ^ 2) :=
      Bounds.Square.add_sq_le_two _ _
    _ ≤ 2 * ((16 : Coordinate) ^ 2 + 256) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add coordinateFourthLe componentSqLe) (by decide)
    _ = 1024 := by ring1

/-- Doubling a coordinate whose square is at most 16 gives square at most 64. -/
private theorem doubledCoordinate_sq_le
    (coordinate : Coordinate) (coordinateSqLe : coordinate ^ 2 ≤ 16) :
    (2 * coordinate) ^ 2 ≤ 64 := by
  calc
    (2 * coordinate) ^ 2 = 4 * coordinate ^ 2 := by ring1
    _ ≤ 4 * 16 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        coordinateSqLe (by decide)
    _ = 64 := by ring1

/-- The exact three-coefficient calculation bounds a quadratic vertical side
majorant by `16384`; this retains the computed `8192 + 8192` rather than
weakening both summands before adding them.

The displayed parameter-square and box-coordinate bounds control both retained real and imaginary quadratic side tables.
Their original rational majorant at one preserves the stated uniform threshold. -/
theorem quadraticVerticalBoundarySideMajorant_le_16384
    (parameter : Gaussian) (x : Coordinate)
    (interval : Data.Rat.Interval.Bounds)
    (intervalSqLe : interval.squareBound ≤ 16)
    (xSqLe : x ^ 2 ≤ 16)
    (parameterNormSqLe :
      Data.Gaussian.Norm.Basic.normSq parameter ≤ 256) :
    Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit
        interval ≤ 16384 := by
  have parameterRealSqLe : parameter.re ^ 2 ≤ 256 :=
    (le_add_of_nonneg_right
      (Fraction.Order.Arithmetic.sq_nonneg_direct parameter.im)).trans
        parameterNormSqLe
  have parameterImagSqLe : parameter.im ^ 2 ≤ 256 :=
    (le_add_of_nonneg_left
      (Fraction.Order.Arithmetic.sq_nonneg_direct parameter.re)).trans
        parameterNormSqLe
  have realConstantSqLe : (x ^ 2 - parameter.re) ^ 2 ≤ 1024 := by
    rw [show x ^ 2 - parameter.re = x ^ 2 + (-parameter.re) by ring1]
    apply coordinateSquare_add_component_sq_le x (-parameter.re) xSqLe
    exact (show (-parameter.re) ^ 2 = parameter.re ^ 2 by ring1).symm ▸ parameterRealSqLe
  have imagConstantSqLe : (-parameter.im) ^ 2 ≤ 1024 := by
    calc
      (-parameter.im) ^ 2 = parameter.im ^ 2 := by ring1
      _ ≤ 256 := parameterImagSqLe
      _ ≤ 1024 := by
        change ((256 : Nat) : Coordinate) ≤ ((1024 : Nat) : Coordinate)
        exact Fraction.Cast.Order.natCast_le_direct (by decide)
  have realLe : Dense.Rational.Bounds.Horner.evalSqBound
      (Dense.Gaussian.Path.Components.pathReal
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit)
      interval ≤ 8192 := by
    rw [quadraticVerticalPathReal_all parameter x]
    apply threeCoefficientHorner_le _ (-1) 0 (x ^ 2 - parameter.re) rfl
      interval intervalSqLe
    · rw [show (-1 : Coordinate) ^ 2 = 1 by ring1]
    · exact (Fraction.Order.Arithmetic.sq_nonneg_direct 0).trans
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 64) (by decide)).le
    · exact realConstantSqLe
  have imaginaryLe : Dense.Rational.Bounds.Horner.evalSqBound
      (Dense.Gaussian.Path.Components.pathImag
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit)
      interval ≤ 8192 := by
    rw [quadraticVerticalPathImag_all parameter x]
    apply threeCoefficientHorner_le _ 0 (2 * x) (-parameter.im) rfl
      interval intervalSqLe
    · exact (Fraction.Order.Arithmetic.sq_nonneg_direct 0).trans
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 1) (by decide)).le
    · exact doubledCoordinate_sq_le x xSqLe
    · exact imagConstantSqLe
  unfold Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
  apply Basic.max_le
  · change ((1 : Nat) : Coordinate) ≤ ((16384 : Nat) : Coordinate)
    exact Fraction.Cast.Order.natCast_le_direct (by decide)
  · calc
      Dense.Rational.Bounds.Horner.evalSqBound
            (Dense.Gaussian.Path.Components.pathReal
              (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
                Riemann.RootContinuation.SquareRootDegree.degreeTwo)
              (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit)
            interval +
          Dense.Rational.Bounds.Horner.evalSqBound
            (Dense.Gaussian.Path.Components.pathImag
              (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
                Riemann.RootContinuation.SquareRootDegree.degreeTwo)
              (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit)
            interval ≤ 8192 + 8192 := add_le_add realLe imaginaryLe
      _ = 16384 := by ring1

/-- Compatibility weakening of the sharp finite vertical-side budget. -/
theorem quadraticVerticalBoundarySideMajorant_le
    (parameter : Gaussian) (x : Coordinate)
    (interval : Data.Rat.Interval.Bounds)
    (intervalSqLe : interval.squareBound ≤ 16)
    (xSqLe : x ^ 2 ≤ 16)
    (parameterNormSqLe :
      Data.Gaussian.Norm.Basic.normSq parameter ≤ 256) :
    Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit
        interval ≤ 65536 :=
  (quadraticVerticalBoundarySideMajorant_le_16384 parameter x
    interval intervalSqLe xSqLe parameterNormSqLe).trans
      (Fraction.Cast.Order.natCast_le_direct (by decide))

/-- Horizontal counterpart of
`quadraticVerticalBoundarySideMajorant_le_16384`.

The displayed parameter-square and box-coordinate bounds control both retained real and imaginary quadratic side tables.
Their original rational majorant at one preserves the stated uniform threshold. -/
theorem quadraticHorizontalBoundarySideMajorant_le_16384
    (parameter : Gaussian) (y : Coordinate)
    (interval : Data.Rat.Interval.Bounds)
    (intervalSqLe : interval.squareBound ≤ 16)
    (ySqLe : y ^ 2 ≤ 16)
    (parameterNormSqLe :
      Data.Gaussian.Norm.Basic.normSq parameter ≤ 256) :
    Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Imaginary.horizontalBase y) Gaussian.Constants.horizontalDirection
        interval ≤ 16384 := by
  have parameterRealSqLe : parameter.re ^ 2 ≤ 256 :=
    (le_add_of_nonneg_right
      (Fraction.Order.Arithmetic.sq_nonneg_direct parameter.im)).trans
        parameterNormSqLe
  have parameterImagSqLe : parameter.im ^ 2 ≤ 256 :=
    (le_add_of_nonneg_left
      (Fraction.Order.Arithmetic.sq_nonneg_direct parameter.re)).trans
        parameterNormSqLe
  have realConstantSqLe : (-(y ^ 2) - parameter.re) ^ 2 ≤ 1024 := by
    rw [show (-(y ^ 2) - parameter.re) ^ 2 =
      (y ^ 2 + parameter.re) ^ 2 by ring1]
    exact coordinateSquare_add_component_sq_le y parameter.re ySqLe
      parameterRealSqLe
  have imagConstantSqLe : (-parameter.im) ^ 2 ≤ 1024 := by
    calc
      (-parameter.im) ^ 2 = parameter.im ^ 2 := by ring1
      _ ≤ 256 := parameterImagSqLe
      _ ≤ 1024 := by
        change ((256 : Nat) : Coordinate) ≤ ((1024 : Nat) : Coordinate)
        exact Fraction.Cast.Order.natCast_le_direct (by decide)
  have realLe : Dense.Rational.Bounds.Horner.evalSqBound
      (Dense.Gaussian.Path.Components.pathReal
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Imaginary.horizontalBase y) Gaussian.Constants.horizontalDirection)
      interval ≤ 8192 := by
    rw [quadraticHorizontalPathReal_all parameter y]
    apply threeCoefficientHorner_le _ 1 0 (-(y ^ 2) - parameter.re) rfl
      interval intervalSqLe
    · rw [show (1 : Coordinate) ^ 2 = 1 by ring1]
    · exact (Fraction.Order.Arithmetic.sq_nonneg_direct 0).trans
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 64) (by decide)).le
    · exact realConstantSqLe
  have imaginaryLe : Dense.Rational.Bounds.Horner.evalSqBound
      (Dense.Gaussian.Path.Components.pathImag
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Imaginary.horizontalBase y) Gaussian.Constants.horizontalDirection)
      interval ≤ 8192 := by
    rw [quadraticHorizontalPathImag_all parameter y]
    apply threeCoefficientHorner_le _ 0 (2 * y) (-parameter.im) rfl
      interval intervalSqLe
    · exact (Fraction.Order.Arithmetic.sq_nonneg_direct 0).trans
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 1) (by decide)).le
    · exact doubledCoordinate_sq_le y ySqLe
    · exact imagConstantSqLe
  unfold Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
  apply Basic.max_le
  · change ((1 : Nat) : Coordinate) ≤ ((16384 : Nat) : Coordinate)
    exact Fraction.Cast.Order.natCast_le_direct (by decide)
  · calc
      Dense.Rational.Bounds.Horner.evalSqBound
            (Dense.Gaussian.Path.Components.pathReal
              (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
                Riemann.RootContinuation.SquareRootDegree.degreeTwo)
              (Gaussian.Cast.Imaginary.horizontalBase y)
                Gaussian.Constants.horizontalDirection)
            interval +
          Dense.Rational.Bounds.Horner.evalSqBound
            (Dense.Gaussian.Path.Components.pathImag
              (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
                Riemann.RootContinuation.SquareRootDegree.degreeTwo)
              (Gaussian.Cast.Imaginary.horizontalBase y)
                Gaussian.Constants.horizontalDirection)
            interval ≤ 8192 + 8192 := add_le_add realLe imaginaryLe
      _ = 16384 := by ring1

/-- Compatibility weakening of the sharp finite horizontal-side budget. -/
theorem quadraticHorizontalBoundarySideMajorant_le
    (parameter : Gaussian) (y : Coordinate)
    (interval : Data.Rat.Interval.Bounds)
    (intervalSqLe : interval.squareBound ≤ 16)
    (ySqLe : y ^ 2 ≤ 16)
    (parameterNormSqLe :
      Data.Gaussian.Norm.Basic.normSq parameter ≤ 256) :
    Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Imaginary.horizontalBase y) Gaussian.Constants.horizontalDirection
        interval ≤ 65536 :=
  (quadraticHorizontalBoundarySideMajorant_le_16384 parameter y
    interval intervalSqLe ySqLe parameterNormSqLe).trans
      (Fraction.Cast.Order.natCast_le_direct (by decide))

/-- A tight finite side budget for the small boxes used by the central
quartic cells.  Keeping the coefficient ceilings symbolic avoids normalizing
the complete executable Horner fold at every concrete grid point.

The displayed parameter-square and box-coordinate bounds control both retained real and imaginary quadratic side tables.
Their original rational majorant at one preserves the stated uniform threshold. -/
theorem quadraticVerticalBoundarySideMajorant_le_256
    (parameter : Gaussian) (x : Coordinate) (xNonzero : x ≠ 0)
    (interval : Data.Rat.Interval.Bounds)
    (intervalSqLe : interval.squareBound ≤ 4)
    (xSqLe : x ^ 2 ≤ 1)
    (parameterNormSqLe :
      Data.Gaussian.Norm.Basic.normSq parameter ≤ 4) :
    Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit
        interval ≤ 256 := by
  have parameterRealSqLe : parameter.re ^ 2 ≤ 4 :=
    (le_add_of_nonneg_right
      (Fraction.Order.Arithmetic.sq_nonneg_direct parameter.im)).trans
        parameterNormSqLe
  have parameterImagSqLe : parameter.im ^ 2 ≤ 4 :=
    (le_add_of_nonneg_left
      (Fraction.Order.Arithmetic.sq_nonneg_direct parameter.re)).trans
        parameterNormSqLe
  have xFourthLe : (x ^ 2) ^ 2 ≤ (1 : Coordinate) ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct
      (Fraction.Order.Arithmetic.sq_nonneg_direct x) xSqLe 2
  have realConstantSqLe : (x ^ 2 - parameter.re) ^ 2 ≤ 10 := by
    rw [show x ^ 2 - parameter.re = x ^ 2 + (-parameter.re) by ring1]
    calc
      (x ^ 2 + -parameter.re) ^ 2 ≤
          2 * ((x ^ 2) ^ 2 + (-parameter.re) ^ 2) :=
        Bounds.Square.add_sq_le_two _ _
      _ ≤ 2 * ((1 : Coordinate) ^ 2 + 4) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add xFourthLe (by exact (show (-parameter.re) ^ 2 = parameter.re ^ 2 by ring1).symm ▸
            parameterRealSqLe))
            (by decide)
      _ = 10 := by ring1
  have doubledXSqLe : (2 * x) ^ 2 ≤ 4 := by
    calc
      (2 * x) ^ 2 = 4 * x ^ 2 := by ring1
      _ ≤ 4 * 1 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct xSqLe
          (by decide)
      _ = 4 := by ring1
  have realLe : Dense.Rational.Bounds.Horner.evalSqBound
      (Dense.Gaussian.Path.Components.pathReal
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit)
      interval ≤ 148 := by
    rw [quadraticVerticalPathReal parameter x xNonzero]
    calc
      Dense.Rational.Bounds.Horner.evalSqBound
          (⟨[-1, 0, x ^ 2 - parameter.re]⟩ : Polynomial) interval ≤
          2 * ((2 * ((2 * (1 : Coordinate)) * 4 + 0)) * 4 + 10) :=
        Dense.Rational.Bounds.Horner.evalSqBound_three_le _ (-1) 0
          (x ^ 2 - parameter.re) rfl interval 4 1 0 10
            (by decide) (by decide) le_rfl intervalSqLe
              (by rw [show (-1 : Coordinate) ^ 2 = 1 by ring1])
                (by rw [zero_pow (by omega : 2 ≠ 0)]) realConstantSqLe
      _ = 148 := by ring1
  have imaginaryLe : Dense.Rational.Bounds.Horner.evalSqBound
      (Dense.Gaussian.Path.Components.pathImag
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit)
      interval ≤ 72 := by
    rw [quadraticVerticalPathImag parameter x xNonzero]
    calc
      Dense.Rational.Bounds.Horner.evalSqBound
          (⟨[0, 2 * x, -parameter.im]⟩ : Polynomial) interval ≤
          2 * ((2 * ((2 * (0 : Coordinate)) * 4 + 4)) * 4 + 4) :=
        Dense.Rational.Bounds.Horner.evalSqBound_three_le _ 0 (2 * x)
          (-parameter.im) rfl interval 4 0 4 4
            (by decide) le_rfl (by decide) intervalSqLe
              (by rw [zero_pow (by omega : 2 ≠ 0)]) doubledXSqLe
                (by exact (show (-parameter.im) ^ 2 = parameter.im ^ 2 by ring1).symm ▸ parameterImagSqLe)
      _ = 72 := by ring1
  unfold Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
  apply Basic.max_le
  · exact Fraction.Cast.Order.natCast_le_direct
      (m := 1) (n := 256) (by omega)
  · calc
      Dense.Rational.Bounds.Horner.evalSqBound
            (Dense.Gaussian.Path.Components.pathReal
              (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
                Riemann.RootContinuation.SquareRootDegree.degreeTwo)
              (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit)
            interval +
          Dense.Rational.Bounds.Horner.evalSqBound
            (Dense.Gaussian.Path.Components.pathImag
              (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
                Riemann.RootContinuation.SquareRootDegree.degreeTwo)
              (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit)
            interval ≤ 148 + 72 := add_le_add realLe imaginaryLe
      _ = 220 := by ring1
      _ ≤ 256 := Fraction.Cast.Order.natCast_le_direct
        (m := 220) (n := 256) (by omega)

/-- Horizontal counterpart of the tight small-box quadratic side budget.

The displayed parameter-square and box-coordinate bounds control both retained real and imaginary quadratic side tables.
Their original rational majorant at one preserves the stated uniform threshold. -/
theorem quadraticHorizontalBoundarySideMajorant_le_256
    (parameter : Gaussian) (y : Coordinate) (yNonzero : y ≠ 0)
    (interval : Data.Rat.Interval.Bounds)
    (intervalSqLe : interval.squareBound ≤ 1)
    (ySqLe : y ^ 2 ≤ 4)
    (parameterNormSqLe :
      Data.Gaussian.Norm.Basic.normSq parameter ≤ 4) :
    Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Imaginary.horizontalBase y) Gaussian.Constants.horizontalDirection
        interval ≤ 256 := by
  have parameterRealSqLe : parameter.re ^ 2 ≤ 4 :=
    (le_add_of_nonneg_right
      (Fraction.Order.Arithmetic.sq_nonneg_direct parameter.im)).trans
        parameterNormSqLe
  have parameterImagSqLe : parameter.im ^ 2 ≤ 4 :=
    (le_add_of_nonneg_left
      (Fraction.Order.Arithmetic.sq_nonneg_direct parameter.re)).trans
        parameterNormSqLe
  have yFourthLe : (y ^ 2) ^ 2 ≤ (4 : Coordinate) ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct
      (Fraction.Order.Arithmetic.sq_nonneg_direct y) ySqLe 2
  have realConstantSqLe : (-(y ^ 2) - parameter.re) ^ 2 ≤ 40 := by
    rw [show (-(y ^ 2) - parameter.re) ^ 2 =
      (y ^ 2 + parameter.re) ^ 2 by ring1]
    calc
      (y ^ 2 + parameter.re) ^ 2 ≤
          2 * ((y ^ 2) ^ 2 + parameter.re ^ 2) := Bounds.Square.add_sq_le_two _ _
      _ ≤ 2 * ((4 : Coordinate) ^ 2 + 4) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add yFourthLe parameterRealSqLe) (by decide)
      _ = 40 := by ring1
  have doubledYSqLe : (2 * y) ^ 2 ≤ 16 := by
    calc
      (2 * y) ^ 2 = 4 * y ^ 2 := by ring1
      _ ≤ 4 * 4 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct ySqLe
          (by decide)
      _ = 16 := by ring1
  have realLe : Dense.Rational.Bounds.Horner.evalSqBound
      (Dense.Gaussian.Path.Components.pathReal
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Imaginary.horizontalBase y) Gaussian.Constants.horizontalDirection)
      interval ≤ 88 := by
    rw [quadraticHorizontalPathReal parameter y yNonzero]
    calc
      Dense.Rational.Bounds.Horner.evalSqBound
          (⟨[1, 0, -(y ^ 2) - parameter.re]⟩ : Polynomial) interval ≤
          2 * ((2 * ((2 * (1 : Coordinate)) * 1 + 0)) * 1 + 40) :=
        Dense.Rational.Bounds.Horner.evalSqBound_three_le _ 1 0
          (-(y ^ 2) - parameter.re) rfl interval 1 1 0 40
            (by decide) (by decide) le_rfl intervalSqLe
              (by rw [one_pow]) (by rw [zero_pow (by omega : 2 ≠ 0)])
                realConstantSqLe
      _ = 88 := by ring1
  have imaginaryLe : Dense.Rational.Bounds.Horner.evalSqBound
      (Dense.Gaussian.Path.Components.pathImag
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Imaginary.horizontalBase y) Gaussian.Constants.horizontalDirection)
      interval ≤ 72 := by
    rw [quadraticHorizontalPathImag parameter y yNonzero]
    calc
      Dense.Rational.Bounds.Horner.evalSqBound
          (⟨[0, 2 * y, -parameter.im]⟩ : Polynomial) interval ≤
          2 * ((2 * ((2 * (0 : Coordinate)) * 1 + 16)) * 1 + 4) :=
        Dense.Rational.Bounds.Horner.evalSqBound_three_le _ 0 (2 * y)
          (-parameter.im) rfl interval 1 0 16 4
            (by decide) le_rfl (by decide) intervalSqLe
              (by rw [zero_pow (by omega : 2 ≠ 0)]) doubledYSqLe
                (by exact (show (-parameter.im) ^ 2 = parameter.im ^ 2 by ring1).symm ▸ parameterImagSqLe)
      _ = 72 := by ring1
  unfold Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
  apply Basic.max_le
  · exact Fraction.Cast.Order.natCast_le_direct
      (m := 1) (n := 256) (by omega)
  · calc
      Dense.Rational.Bounds.Horner.evalSqBound
            (Dense.Gaussian.Path.Components.pathReal
              (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
                Riemann.RootContinuation.SquareRootDegree.degreeTwo)
              (Gaussian.Cast.Imaginary.horizontalBase y)
                Gaussian.Constants.horizontalDirection)
            interval +
          Dense.Rational.Bounds.Horner.evalSqBound
            (Dense.Gaussian.Path.Components.pathImag
              (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
                Riemann.RootContinuation.SquareRootDegree.degreeTwo)
              (Gaussian.Cast.Imaginary.horizontalBase y)
                Gaussian.Constants.horizontalDirection)
            interval ≤ 88 + 72 := add_le_add realLe imaginaryLe
      _ = 160 := by ring1
      _ ≤ 256 := Fraction.Cast.Order.natCast_le_direct
        (m := 160) (n := 256) (by omega)

/-- A medium finite side budget for a vertically elongated quadratic box.
This is the certificate shape used by the reverse outer horizontal cells:
the vertical coordinate may have square as large as `6`, while the fixed
horizontal coordinate remains inside the unit square.

The displayed parameter-square and box-coordinate bounds control both retained real and imaginary quadratic side tables.
Their original rational majorant at one preserves the stated uniform threshold. -/
theorem quadraticVerticalBoundarySideMajorant_le_1024
    (parameter : Gaussian) (x : Coordinate) (xNonzero : x ≠ 0)
    (interval : Data.Rat.Interval.Bounds)
    (intervalSqLe : interval.squareBound ≤ 6)
    (xSqLe : x ^ 2 ≤ 1)
    (parameterNormSqLe :
      Data.Gaussian.Norm.Basic.normSq parameter ≤ 4) :
    Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit
        interval ≤ 1024 := by
  have parameterRealSqLe : parameter.re ^ 2 ≤ 4 :=
    (le_add_of_nonneg_right
      (Fraction.Order.Arithmetic.sq_nonneg_direct parameter.im)).trans
        parameterNormSqLe
  have parameterImagSqLe : parameter.im ^ 2 ≤ 4 :=
    (le_add_of_nonneg_left
      (Fraction.Order.Arithmetic.sq_nonneg_direct parameter.re)).trans
        parameterNormSqLe
  have xFourthLe : (x ^ 2) ^ 2 ≤ (1 : Coordinate) ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct
      (Fraction.Order.Arithmetic.sq_nonneg_direct x) xSqLe 2
  have realConstantSqLe : (x ^ 2 - parameter.re) ^ 2 ≤ 10 := by
    rw [show x ^ 2 - parameter.re = x ^ 2 + (-parameter.re) by ring1]
    calc
      (x ^ 2 + -parameter.re) ^ 2 ≤
          2 * ((x ^ 2) ^ 2 + (-parameter.re) ^ 2) :=
        Bounds.Square.add_sq_le_two _ _
      _ ≤ 2 * ((1 : Coordinate) ^ 2 + 4) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add xFourthLe (by exact (show (-parameter.re) ^ 2 = parameter.re ^ 2 by ring1).symm ▸
            parameterRealSqLe))
            (by decide)
      _ = 10 := by ring1
  have doubledXSqLe : (2 * x) ^ 2 ≤ 4 := by
    calc
      (2 * x) ^ 2 = 4 * x ^ 2 := by ring1
      _ ≤ 4 * 1 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct xSqLe
          (by decide)
      _ = 4 := by ring1
  have realLe : Dense.Rational.Bounds.Horner.evalSqBound
      (Dense.Gaussian.Path.Components.pathReal
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit)
      interval ≤ 308 := by
    rw [quadraticVerticalPathReal parameter x xNonzero]
    calc
      Dense.Rational.Bounds.Horner.evalSqBound
          (⟨[-1, 0, x ^ 2 - parameter.re]⟩ : Polynomial) interval ≤
          2 * ((2 * ((2 * (1 : Coordinate)) * 6 + 0)) * 6 + 10) :=
        Dense.Rational.Bounds.Horner.evalSqBound_three_le _ (-1) 0
          (x ^ 2 - parameter.re) rfl interval 6 1 0 10
            (by decide) (by decide) le_rfl intervalSqLe
              (by rw [show (-1 : Coordinate) ^ 2 = 1 by ring1])
                (by rw [zero_pow (by omega : 2 ≠ 0)]) realConstantSqLe
      _ = 308 := by ring1
  have imaginaryLe : Dense.Rational.Bounds.Horner.evalSqBound
      (Dense.Gaussian.Path.Components.pathImag
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit)
      interval ≤ 104 := by
    rw [quadraticVerticalPathImag parameter x xNonzero]
    calc
      Dense.Rational.Bounds.Horner.evalSqBound
          (⟨[0, 2 * x, -parameter.im]⟩ : Polynomial) interval ≤
          2 * ((2 * ((2 * (0 : Coordinate)) * 6 + 4)) * 6 + 4) :=
        Dense.Rational.Bounds.Horner.evalSqBound_three_le _ 0 (2 * x)
          (-parameter.im) rfl interval 6 0 4 4
            (by decide) le_rfl (by decide) intervalSqLe
              (by rw [zero_pow (by omega : 2 ≠ 0)]) doubledXSqLe
                (by exact (show (-parameter.im) ^ 2 = parameter.im ^ 2 by ring1).symm ▸ parameterImagSqLe)
      _ = 104 := by ring1
  unfold Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
  apply Basic.max_le
  · exact Fraction.Cast.Order.natCast_le_direct
      (m := 1) (n := 1024) (by omega)
  · calc
      Dense.Rational.Bounds.Horner.evalSqBound
            (Dense.Gaussian.Path.Components.pathReal
              (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
                Riemann.RootContinuation.SquareRootDegree.degreeTwo)
              (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit)
            interval +
          Dense.Rational.Bounds.Horner.evalSqBound
            (Dense.Gaussian.Path.Components.pathImag
              (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
                Riemann.RootContinuation.SquareRootDegree.degreeTwo)
              (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit)
            interval ≤ 308 + 104 := add_le_add realLe imaginaryLe
      _ = 412 := by ring1
      _ ≤ 1024 := Fraction.Cast.Order.natCast_le_direct
        (m := 412) (n := 1024) (by omega)

/-- Horizontal counterpart of
`quadraticVerticalBoundarySideMajorant_le_1024`, with the long coordinate
fixed and the varying coordinate inside the unit square.

The displayed parameter-square and box-coordinate bounds control both retained real and imaginary quadratic side tables.
Their original rational majorant at one preserves the stated uniform threshold. -/
theorem quadraticHorizontalBoundarySideMajorant_le_1024
    (parameter : Gaussian) (y : Coordinate) (yNonzero : y ≠ 0)
    (interval : Data.Rat.Interval.Bounds)
    (intervalSqLe : interval.squareBound ≤ 1)
    (ySqLe : y ^ 2 ≤ 6)
    (parameterNormSqLe :
      Data.Gaussian.Norm.Basic.normSq parameter ≤ 4) :
    Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Imaginary.horizontalBase y) Gaussian.Constants.horizontalDirection
        interval ≤ 1024 := by
  have parameterRealSqLe : parameter.re ^ 2 ≤ 4 :=
    (le_add_of_nonneg_right
      (Fraction.Order.Arithmetic.sq_nonneg_direct parameter.im)).trans
        parameterNormSqLe
  have parameterImagSqLe : parameter.im ^ 2 ≤ 4 :=
    (le_add_of_nonneg_left
      (Fraction.Order.Arithmetic.sq_nonneg_direct parameter.re)).trans
        parameterNormSqLe
  have yFourthLe : (y ^ 2) ^ 2 ≤ (6 : Coordinate) ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct
      (Fraction.Order.Arithmetic.sq_nonneg_direct y) ySqLe 2
  have realConstantSqLe : (-(y ^ 2) - parameter.re) ^ 2 ≤ 80 := by
    rw [show (-(y ^ 2) - parameter.re) ^ 2 =
      (y ^ 2 + parameter.re) ^ 2 by ring1]
    calc
      (y ^ 2 + parameter.re) ^ 2 ≤
          2 * ((y ^ 2) ^ 2 + parameter.re ^ 2) := Bounds.Square.add_sq_le_two _ _
      _ ≤ 2 * ((6 : Coordinate) ^ 2 + 4) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add yFourthLe parameterRealSqLe) (by decide)
      _ = 80 := by ring1
  have doubledYSqLe : (2 * y) ^ 2 ≤ 24 := by
    calc
      (2 * y) ^ 2 = 4 * y ^ 2 := by ring1
      _ ≤ 4 * 6 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct ySqLe
          (by decide)
      _ = 24 := by ring1
  have realLe : Dense.Rational.Bounds.Horner.evalSqBound
      (Dense.Gaussian.Path.Components.pathReal
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Imaginary.horizontalBase y) Gaussian.Constants.horizontalDirection)
      interval ≤ 168 := by
    rw [quadraticHorizontalPathReal parameter y yNonzero]
    calc
      Dense.Rational.Bounds.Horner.evalSqBound
          (⟨[1, 0, -(y ^ 2) - parameter.re]⟩ : Polynomial) interval ≤
          2 * ((2 * ((2 * (1 : Coordinate)) * 1 + 0)) * 1 + 80) :=
        Dense.Rational.Bounds.Horner.evalSqBound_three_le _ 1 0
          (-(y ^ 2) - parameter.re) rfl interval 1 1 0 80
            (by decide) (by decide) le_rfl intervalSqLe
              (by rw [one_pow]) (by rw [zero_pow (by omega : 2 ≠ 0)])
                realConstantSqLe
      _ = 168 := by ring1
  have imaginaryLe : Dense.Rational.Bounds.Horner.evalSqBound
      (Dense.Gaussian.Path.Components.pathImag
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Imaginary.horizontalBase y) Gaussian.Constants.horizontalDirection)
      interval ≤ 104 := by
    rw [quadraticHorizontalPathImag parameter y yNonzero]
    calc
      Dense.Rational.Bounds.Horner.evalSqBound
          (⟨[0, 2 * y, -parameter.im]⟩ : Polynomial) interval ≤
          2 * ((2 * ((2 * (0 : Coordinate)) * 1 + 24)) * 1 + 4) :=
        Dense.Rational.Bounds.Horner.evalSqBound_three_le _ 0 (2 * y)
          (-parameter.im) rfl interval 1 0 24 4
            (by decide) le_rfl (by decide) intervalSqLe
              (by rw [zero_pow (by omega : 2 ≠ 0)]) doubledYSqLe
                (by exact (show (-parameter.im) ^ 2 = parameter.im ^ 2 by ring1).symm ▸ parameterImagSqLe)
      _ = 104 := by ring1
  unfold Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
  apply Basic.max_le
  · exact Fraction.Cast.Order.natCast_le_direct
      (m := 1) (n := 1024) (by omega)
  · calc
      Dense.Rational.Bounds.Horner.evalSqBound
            (Dense.Gaussian.Path.Components.pathReal
              (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
                Riemann.RootContinuation.SquareRootDegree.degreeTwo)
              (Gaussian.Cast.Imaginary.horizontalBase y)
                Gaussian.Constants.horizontalDirection)
            interval +
          Dense.Rational.Bounds.Horner.evalSqBound
            (Dense.Gaussian.Path.Components.pathImag
              (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
                Riemann.RootContinuation.SquareRootDegree.degreeTwo)
              (Gaussian.Cast.Imaginary.horizontalBase y)
                Gaussian.Constants.horizontalDirection)
            interval ≤ 168 + 104 := add_le_add realLe imaginaryLe
      _ = 272 := by ring1
      _ ≤ 1024 := Fraction.Cast.Order.natCast_le_direct
        (m := 272) (n := 1024) (by omega)

/-- Direct quadratic boundary clearance using the four explicit side
resultants. -/
@[expose] def directBoundaryClearance (parameter : Gaussian) (box : QuadraticBox)
    (leftNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter box.xLower ≠ 0)
    (rightNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter box.xUpper ≠ 0)
    (bottomNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter box.yLower ≠ 0)
    (topNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter box.yUpper ≠ 0) :
    BoundaryClearance (rootPolynomial parameter) box :=
  Clearance.Box.Boundary.Lines.boundaryOfLines
    (SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directVerticalClearance parameter box
      box.xLower leftNonzero)
    (SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directVerticalClearance parameter box
      box.xUpper rightNonzero)
    (SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directHorizontalClearance parameter box
      box.yLower bottomNonzero)
    (SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directHorizontalClearance parameter box
      box.yUpper topNonzero)

/-- The retained direct quadratic boundary bound is exactly the minimum of its four original resultant side bounds. -/
@[simp] theorem directBoundaryClearance_bound
    (parameter : Gaussian) (box : QuadraticBox)
    (leftNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter box.xLower ≠ 0)
    (rightNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter box.xUpper ≠ 0)
    (bottomNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter box.yLower ≠ 0)
    (topNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter box.yUpper ≠ 0) :
    (directBoundaryClearance parameter box leftNonzero rightNonzero
      bottomNonzero topNonzero).bound =
      min (SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directVerticalClearanceBound
        parameter box box.xLower)
        (min (SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directVerticalClearanceBound
          parameter box box.xUpper)
          (min (SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
            parameter box box.yLower)
            (SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
              parameter box box.yUpper))) := rfl

/-- A displayed rational value below all four direct side bounds is below the
cached quadratic boundary clearance. -/
theorem le_directBoundaryClearance_bound
    (parameter : Gaussian) (box : QuadraticBox)
    (leftNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter box.xLower ≠ 0)
    (rightNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter box.xUpper ≠ 0)
    (bottomNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter box.yLower ≠ 0)
    (topNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter box.yUpper ≠ 0)
    (lower : Coordinate)
    (leftLe : lower ≤
      SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directVerticalClearanceBound parameter
      box box.xLower)
    (rightLe : lower ≤
      SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directVerticalClearanceBound parameter
      box box.xUpper)
    (bottomLe :
      lower ≤ SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
        parameter box box.yLower)
    (topLe : lower ≤
      SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directHorizontalClearanceBound parameter
      box box.yUpper) :
    lower ≤ (directBoundaryClearance parameter box leftNonzero rightNonzero
      bottomNonzero topNonzero).bound := by
  rw [directBoundaryClearance_bound]
  exact le_min leftLe (le_min rightLe (le_min bottomLe topLe))

/-- Cached lower and upper bounds for the exact four-resultant clearance of a
quadratic owner box.  Concrete examples can compute this finite record once
and reuse it through preparation and transport. -/
structure DirectBoundaryBounds (parameter : Gaussian) (box : QuadraticBox)
    (lower upper : Coordinate) where
  /-- The exact left side resultant of the retained quadratic box is nonzero. -/ leftNonzero :
    SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
      parameter box.xLower ≠ 0
  /-- The exact right side resultant of the retained quadratic box is nonzero. -/ rightNonzero :
    SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
      parameter box.xUpper ≠ 0
  /-- The exact bottom side resultant of the retained quadratic box is nonzero. -/ bottomNonzero :
    SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
      parameter box.yLower ≠ 0
  /-- The exact top side resultant of the retained quadratic box is nonzero. -/ topNonzero :
    SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
      parameter box.yUpper ≠ 0
  /-- The supplied lower bound is no larger than the retained four-resultant clearance. -/ lower_le : lower ≤
    (directBoundaryClearance parameter box leftNonzero rightNonzero
      bottomNonzero topNonzero).bound
  /-- The retained four-resultant clearance is no larger than the supplied upper bound. -/ le_upper :
    (directBoundaryClearance parameter box leftNonzero rightNonzero
      bottomNonzero topNonzero).bound ≤ upper

/-- Assemble a direct-bound cache from the four exact side comparisons and
one upper comparison of their minimum. -/
theorem directBoundaryBoundsOfSideChecks
    (parameter : Gaussian) (box : QuadraticBox) (lower upper : Coordinate)
    (leftNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter box.xLower ≠ 0)
    (rightNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter box.xUpper ≠ 0)
    (bottomNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter box.yLower ≠ 0)
    (topNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter box.yUpper ≠ 0)
    (leftLower : lower ≤
      SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directVerticalClearanceBound parameter
        box box.xLower)
    (rightLower : lower ≤
      SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directVerticalClearanceBound parameter
        box box.xUpper)
    (bottomLower : lower ≤
      SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directHorizontalClearanceBound parameter
        box box.yLower)
    (topLower : lower ≤
      SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directHorizontalClearanceBound parameter
        box box.yUpper)
    (upperBound :
      min (SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directVerticalClearanceBound
        parameter box box.xLower)
        (min (SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directVerticalClearanceBound
          parameter box box.xUpper)
          (min (SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
            parameter box box.yLower)
            (SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
              parameter box box.yUpper))) ≤
        upper) :
    DirectBoundaryBounds parameter box lower upper := by
  refine
    { leftNonzero := leftNonzero
      rightNonzero := rightNonzero
      bottomNonzero := bottomNonzero
      topNonzero := topNonzero
      lower_le := ?_
      le_upper := ?_ }
  · exact le_directBoundaryClearance_bound parameter box leftNonzero
      rightNonzero bottomNonzero topNonzero lower leftLower rightLower
        bottomLower topLower
  · rw [directBoundaryClearance_bound]
    exact upperBound

/-- The rational midpoint of the displayed interval endpoints. -/
@[expose] def midpoint (lower upper : Coordinate) : Fraction.Rational :=
  (lower + upper) / 2

/-- The rational midpoint lies strictly between two strictly ordered endpoints. -/
theorem midpoint_strict {lower upper : Coordinate}
    (proper : lower < upper) :
    lower < midpoint lower upper ∧ midpoint lower upper <
      upper := by
  constructor
  · apply (Fraction.Order.Field.lt_div_iff_pos
      (by decide : (0 : Coordinate) < 2)).2
    calc
      lower * 2 = lower + lower := by ring1
      _ < lower + upper :=
        Fraction.Order.Arithmetic.add_lt_add_left_direct proper lower
  · apply (Fraction.Order.Field.div_lt_iff_pos
      (by decide : (0 : Coordinate) < 2)).2
    calc
      lower + upper < upper + upper :=
        Fraction.Order.Arithmetic.add_lt_add_right_direct proper upper
      _ = upper * 2 := by ring1

/-- The rational point one sixteenth of the interval width above its lower endpoint. -/
@[expose] def insetLower (lower upper : Coordinate) : Fraction.Rational :=
  midpoint lower
    (midpoint lower (midpoint lower
      (midpoint lower upper)))

/-- The rational point one sixteenth of the interval width below its upper endpoint. -/
@[expose] def insetUpper (lower upper : Coordinate) : Fraction.Rational :=
  midpoint
    (midpoint (midpoint (midpoint
      lower upper) upper) upper) upper

/-- The lower inset lies strictly between the original lower endpoint and midpoint. -/
theorem insetLower_strict {lower upper : Coordinate}
    (proper : lower < upper) :
    lower < insetLower lower upper ∧
      insetLower lower upper < midpoint lower upper := by
  let half := midpoint lower upper
  let quarter := midpoint lower half
  let eighth := midpoint lower quarter
  have lowerHalf := midpoint_strict proper
  have lowerQuarter := midpoint_strict lowerHalf.1
  have lowerEighth := midpoint_strict lowerQuarter.1
  have lowerSixteenth := midpoint_strict lowerEighth.1
  exact ⟨lowerSixteenth.1,
    lowerSixteenth.2.trans
      (lowerEighth.2.trans lowerQuarter.2)⟩

/-- The upper inset lies strictly between the original midpoint and upper endpoint. -/
theorem insetUpper_strict {lower upper : Coordinate}
    (proper : lower < upper) :
    midpoint lower upper < insetUpper lower upper ∧
      insetUpper lower upper < upper := by
  let half := midpoint lower upper
  let threeQuarter := midpoint half upper
  let sevenEighth := midpoint threeQuarter upper
  have halfUpper := midpoint_strict proper
  have quarterUpper := midpoint_strict halfUpper.2
  have eighthUpper := midpoint_strict quarterUpper.2
  have sixteenthUpper := midpoint_strict eighthUpper.2
  exact ⟨quarterUpper.1.trans
      (eighthUpper.1.trans sixteenthUpper.1),
    sixteenthUpper.2⟩

/-- A fixed strict inset retaining seven eighths of each original coordinate interval.

Each side moves inward by one sixteenth of its original width; the caller separately checks winding before using the box
as a refinement source. -/
@[expose] def strictInsetBox (box : QuadraticBox) (proper : box.Proper) : QuadraticBox where
  xLower := insetLower box.xLower box.xUpper
  xUpper := insetUpper box.xLower box.xUpper
  yLower := insetLower box.yLower box.yUpper
  yUpper := insetUpper box.yLower box.yUpper
  x_valid := ((insetLower_strict proper.1).2.trans
    (insetUpper_strict proper.1).1).le
  y_valid := ((insetLower_strict proper.2).2.trans
    (insetUpper_strict proper.2).1).le

/-- The fixed rational inset lies strictly inside the original proper box. -/
theorem strictInsetBox_strict (box : QuadraticBox) (proper : box.Proper) :
    (strictInsetBox box proper).StrictInterior box :=
  ⟨(insetLower_strict proper.1).1, (insetUpper_strict
    proper.1).2,
    (insetLower_strict proper.2).1, (insetUpper_strict
      proper.2).2⟩

/-- The fixed inset of a proper rational box remains proper. -/
theorem strictInsetBox_proper (box : QuadraticBox) (proper : box.Proper) :
    (strictInsetBox box proper).Proper :=
  ⟨(insetLower_strict proper.1).2.trans (insetUpper_strict
    proper.1).1,
    (insetLower_strict proper.2).2.trans (insetUpper_strict
      proper.2).1⟩

set_option genInjectivity false in
/-- A retained proper box strictly inside the original winding-one state box.

The retained box, properness and strict-interior witness concern the same original winding-one current state. -/
structure StrictInsetData {parameter : Gaussian} {ambient : QuadraticBox}
    (current : WindingOneState
      (rootPolynomial parameter) ambient) where
  /-- The actual rational inset box. -/ box : QuadraticBox
  /-- The retained inset box lies strictly inside the original state box. -/ strict : box.StrictInterior current.box
  /-- Both intervals of the retained inset box are proper. -/ proper : box.Proper

constructive_injectivity StrictInsetData

/-- A much narrower strict inset whose margin is a finite dyadic number below
the current protected-boundary radius.  Keeping the displayed margin dyadic
prevents repeated strict-nesting requests from copying the full exact
clearance denominator into all four box coordinates.

The retained dyadic radius is selected below the original protected-boundary radius. Its same four coordinate
translations give the cached proper box and strict interior witness. -/
@[expose] def protectedStrictInset {parameter : Gaussian} {ambient : QuadraticBox}
    (current : WindingOneState
      (rootPolynomial parameter) ambient) : StrictInsetData
        current := by
  let safeRadius := Clearance.Box.ProtectedRadius.protectedBoundaryRadius
    (rootPolynomial parameter) current.box current.clearance
  have safeRadiusPositive : 0 < safeRadius :=
    Clearance.Box.ProtectedRadius.protectedBoundaryRadius_pos
      (rootPolynomial parameter) current.clearance current.proper
  let rho := Approximation.Rational.Geometric.Basic.quarterRadius 1
    (Approximation.Rational.Geometric.Search.firstQuarterBelow 1 0 safeRadius)
  have rhoPositive : 0 < rho :=
    Approximation.Rational.Geometric.Basic.quarterRadius_pos (by decide) _
  have rhoLeSafeRadius : rho ≤ safeRadius := by
    exact (Approximation.Rational.Geometric.Search.firstQuarterBelow_accurate 1 (by decide) 0
      safeRadius safeRadiusPositive).le
  have widthBounds :=
    Clearance.Box.ProtectedRadius.protectedBoundaryRadius_le_widths
      (rootPolynomial parameter) current.box current.clearance
  have safeScaledX : safeRadius * 16 ≤ current.box.widthX :=
    (Fraction.Order.Field.le_div_iff_pos
      (show (0 : Coordinate) < 16 by decide)).mp widthBounds.1
  have safeScaledY : safeRadius * 16 ≤ current.box.widthY :=
    (Fraction.Order.Field.le_div_iff_pos
      (show (0 : Coordinate) < 16 by decide)).mp widthBounds.2
  have scaledX : rho * 16 ≤ current.box.widthX :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      rhoLeSafeRadius (by decide)).trans safeScaledX
  have scaledY : rho * 16 ≤ current.box.widthY :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      rhoLeSafeRadius (by decide)).trans safeScaledY
  have twiceX : 2 * rho < current.box.widthX := by
    calc
      2 * rho < 16 * rho :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
          (by decide) rhoPositive
      _ = rho * 16 := by ring1
      _ ≤ current.box.widthX := scaledX
  have twiceY : 2 * rho < current.box.widthY := by
    calc
      2 * rho < 16 * rho :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
          (by decide) rhoPositive
      _ = rho * 16 := by ring1
      _ ≤ current.box.widthY := scaledY
  have xProper : current.box.xLower + rho < current.box.xUpper - rho := by
    apply Fraction.Order.Arithmetic.lt_of_add_lt_add_right_direct (c := rho)
    calc
      current.box.xLower + rho + rho =
          current.box.xLower + 2 * rho := by ring1
      _ < current.box.xLower + current.box.widthX :=
        Fraction.Order.Arithmetic.add_lt_add_left_direct twiceX _
      _ = current.box.xUpper := by
        unfold Box.widthX
        ring1
      _ = current.box.xUpper - rho + rho := by ring1
  have yProper : current.box.yLower + rho < current.box.yUpper - rho := by
    apply Fraction.Order.Arithmetic.lt_of_add_lt_add_right_direct (c := rho)
    calc
      current.box.yLower + rho + rho =
          current.box.yLower + 2 * rho := by ring1
      _ < current.box.yLower + current.box.widthY :=
        Fraction.Order.Arithmetic.add_lt_add_left_direct twiceY _
      _ = current.box.yUpper := by
        unfold Box.widthY
        ring1
      _ = current.box.yUpper - rho + rho := by ring1
  let box : QuadraticBox :=
    { xLower := current.box.xLower + rho
      xUpper := current.box.xUpper - rho
      yLower := current.box.yLower + rho
      yUpper := current.box.yUpper - rho
      x_valid := xProper.le
      y_valid := yProper.le }
  have left : current.box.xLower < box.xLower := by
    change current.box.xLower < current.box.xLower + rho
    have translated := Fraction.Order.Arithmetic.add_lt_add_left_direct rhoPositive current.box.xLower
    rw [_root_.add_zero] at translated
    exact translated
  have right : box.xUpper < current.box.xUpper := by
    change current.box.xUpper - rho < current.box.xUpper
    have translated := Fraction.Order.Arithmetic.sub_lt_sub_left_direct rhoPositive current.box.xUpper
    have zeroSub : current.box.xUpper - (0 : Coordinate) = current.box.xUpper := by ring1
    rw [zeroSub] at translated
    exact translated
  have bottom : current.box.yLower < box.yLower := by
    change current.box.yLower < current.box.yLower + rho
    have translated := Fraction.Order.Arithmetic.add_lt_add_left_direct rhoPositive current.box.yLower
    rw [_root_.add_zero] at translated
    exact translated
  have top : box.yUpper < current.box.yUpper := by
    change current.box.yUpper - rho < current.box.yUpper
    have translated := Fraction.Order.Arithmetic.sub_lt_sub_left_direct rhoPositive current.box.yUpper
    have zeroSub : current.box.yUpper - (0 : Coordinate) = current.box.yUpper := by ring1
    rw [zeroSub] at translated
    exact translated
  exact
    { box := box
      strict := ⟨left, right, bottom, top⟩
      proper := ⟨xProper, yProper⟩ }

set_option genInjectivity false in
/-- Proof-bearing result of the direct quadratic refinement attempt.

The retained refined state is indexed by the same original current state and exact positive rational accuracy request.
-/
structure FastRefinement {parameter : Gaussian} {ambient : QuadraticBox}
    (current : WindingOneState
      (rootPolynomial parameter) ambient)
    (epsilon : Coordinate) where
  /-- The actual retained winding-one state returned by the finite refinement. -/ state :
    WindingOneState
    (rootPolynomial parameter) ambient
  /-- The returned state box refines the original state box. -/ nested : state.box.Refines current.box
  /-- The returned state box lies strictly inside the original state box. -/ strict : state.box.StrictInterior
    current.box
  /-- The returned state box meets the original requested squared-diagonal bound. -/ accurate : state.box.diagonalSq ≤
    epsilon ^ 2

constructive_injectivity FastRefinement

/-- The direct raw-subdivision target is exactly the caller's requested
squared diameter.  Strict nesting is checked separately, first on the raw
candidate and then through one of the certified inset sources. -/
@[expose] def fastRefinementTarget {parameter : Gaussian} {ambient : QuadraticBox}
    (_current : WindingOneState
      (rootPolynomial parameter) ambient)
    (epsilon : Coordinate) : Fraction.Rational :=
  epsilon ^ 2

/-- A positive requested accuracy gives a positive squared-diagonal refinement target. -/
theorem fastRefinementTarget_positive {parameter : Gaussian}
    {ambient : QuadraticBox}
    (current : WindingOneState
      (rootPolynomial parameter) ambient)
    {epsilon : Coordinate} (positive : 0 < epsilon) :
    0 < fastRefinementTarget current epsilon := by
  unfold fastRefinementTarget
  exact Fraction.Order.Arithmetic.pow_pos_direct positive 2

set_option genInjectivity false in
/-- A retained nonzero-winding raw state strictly inside the original winding-one box.

The original current state indexes the retained raw inset and its exact strict-interior evidence. -/
structure StrictRawInset {parameter : Gaussian} {ambient : QuadraticBox}
    (current : WindingOneState
      (rootPolynomial parameter) ambient) where
  /-- The actual retained raw winding state on the original ambient. -/ state : State.Raw.RawWindingState
    (rootPolynomial parameter) ambient
  /-- The retained raw-state box lies strictly inside the original winding-one box. -/ strict : state.box.StrictInterior
    current.box

constructive_injectivity StrictRawInset

/-- Check one supplied strict inset and retain it only when its four sides are
root-free and its winding is the selected quadratic occurrence. -/
@[expose] def checkedRawInset? {parameter : Gaussian} {ambient : QuadraticBox}
    (current : WindingOneState
      (rootPolynomial parameter) ambient)
    (inset : StrictInsetData current) :
    Option (StrictRawInset current) := by
  let box := inset.box
  if leftNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter box.xLower ≠ 0 then
    if rightNonzero :
        SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
          parameter box.xUpper ≠ 0 then
      if bottomNonzero :
          SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
            parameter box.yLower ≠ 0 then
        if topNonzero :
            SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
              parameter box.yUpper ≠ 0 then
          if windingFour : Winding.Box.Basic.quadrupledBoxWinding
              (rootPolynomial parameter) box = 4 then
            exact some
              { state :=
                  { box := box
                    refinesAmbient := (Geometry.Rational.Box.Refinement.StrictInterior.refines inset.strict).trans
                      current.refinesAmbient
                    proper := inset.proper
                    clearance := directBoundaryClearance parameter box
                      leftNonzero rightNonzero bottomNonzero topNonzero
                    rawWinding_ne := by
                      rw [windingFour]
                      decide }
                strict := inset.strict }
          else exact none
        else exact none
      else exact none
    else exact none
  else exact none

/-- Check the cheap fixed inset first, then retry with the much narrower
clearance-scaled inset.  Failure remains harmless because the caller retains
its total generic fallback. -/
@[expose] def strictRawInset? {parameter : Gaussian} {ambient : QuadraticBox}
    (current : WindingOneState
      (rootPolynomial parameter) ambient) :
    Option (StrictRawInset current) :=
  let fixed : StrictInsetData current :=
    { box := strictInsetBox current.box current.proper
      strict := strictInsetBox_strict current.box current.proper
      proper := strictInsetBox_proper current.box current.proper }
  match checkedRawInset? current fixed with
  | some inset => some inset
  | none => checkedRawInset? current (protectedStrictInset
    current)

/-- Recheck a raw quadratic candidate and promote it to the complete strict
track-state interface. -/
@[expose] def checkedFastRefinement? {parameter : Gaussian} {ambient : QuadraticBox}
    (current : WindingOneState
      (rootPolynomial parameter) ambient)
    (epsilon : Coordinate)
    (candidate : State.Raw.RawWindingState
      (rootPolynomial parameter) ambient)
    (strict : candidate.box.StrictInterior current.box)
    (accurate : candidate.box.diagonalSq ≤ epsilon ^ 2) :
    Option (FastRefinement current epsilon) := by
  if leftNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter candidate.box.xLower ≠ 0 then
    if rightNonzero :
        SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
          parameter candidate.box.xUpper ≠ 0 then
      if bottomNonzero :
          SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
            parameter candidate.box.yLower ≠ 0 then
        if topNonzero :
            SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
              parameter candidate.box.yUpper ≠ 0 then
          if windingFour : Winding.Box.Basic.quadrupledBoxWinding
              (rootPolynomial parameter) candidate.box = 4 then
            let clearance := directBoundaryClearance parameter candidate.box
              leftNonzero rightNonzero bottomNonzero topNonzero
            let state : WindingOneState
                (rootPolynomial parameter) ambient :=
              { box := candidate.box
                refinesAmbient := candidate.refinesAmbient
                proper := candidate.proper
                clearance := clearance
                rawWindingFour := windingFour
                ambientLeftClearance :=
                  SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directVerticalClearance
                    parameter ambient
                    candidate.box.xLower leftNonzero
                ambientRightClearance :=
                  SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directVerticalClearance
                    parameter ambient
                    candidate.box.xUpper rightNonzero
                ambientBottomClearance :=
                  SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directHorizontalClearance
                    parameter ambient
                    candidate.box.yLower bottomNonzero
                ambientTopClearance :=
                  SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directHorizontalClearance
                    parameter ambient
                    candidate.box.yUpper topNonzero }
            exact some
              { state := state
                nested := (Geometry.Rational.Box.Refinement.StrictInterior.refines strict)
                strict := strict
                accurate := accurate }
          else exact none
        else exact none
      else exact none
    else exact none
  else exact none

/-- Try the much cheaper direct quadratic subdivision before invoking the
generic Newton-band fallback.  Every successful branch rechecks all four
global side resultants and winding four, so the returned track state has the
same full interface as the generic extractor. -/
@[expose] def subdivisionRefinement? {parameter : Gaussian} {ambient : QuadraticBox}
    (current : WindingOneState
      (rootPolynomial parameter) ambient)
    (epsilon : Coordinate) (positive : 0 < epsilon) :
    Option (FastRefinement current epsilon) := by
  let initial := current.raw
  let target := fastRefinementTarget current epsilon
  let candidate := Subdivision.Raw.Request.refineTo
    (SquareRoot.Clearance.QuadraticAxisElimination.quadraticAxisElimination parameter) initial target
  have candidateAccurate : candidate.box.diagonalSq ≤ epsilon ^ 2 :=
    Subdivision.Raw.Request.refineTo_diagonalSq_le
      (SquareRoot.Clearance.QuadraticAxisElimination.quadraticAxisElimination parameter) initial
      (fastRefinementTarget_positive current positive)
  if strict : candidate.box.StrictInterior current.box then
    exact checkedFastRefinement? current epsilon candidate strict
      candidateAccurate
  else
    match strictRawInset? current with
    | none => exact none
    | some inset =>
        let insetCandidate := Subdivision.Raw.Request.refineTo
          (SquareRoot.Clearance.QuadraticAxisElimination.quadraticAxisElimination parameter) inset.state target
        have insetRefines : insetCandidate.box.Refines inset.state.box :=
          Subdivision.Raw.Request.refineTo_refines
            (SquareRoot.Clearance.QuadraticAxisElimination.quadraticAxisElimination parameter) inset.state target
        have insetStrict : insetCandidate.box.StrictInterior current.box :=
          (Geometry.Rational.Box.Refinement.StrictInterior.of_refines inset.strict) insetRefines
        have insetAccurate : insetCandidate.box.diagonalSq ≤ epsilon ^ 2 :=
          Subdivision.Raw.Request.refineTo_diagonalSq_le
            (SquareRoot.Clearance.QuadraticAxisElimination.quadraticAxisElimination parameter) inset.state
            (fastRefinementTarget_positive current positive)
        exact checkedFastRefinement? current epsilon insetCandidate insetStrict
          insetAccurate

/-- Try checked Newton centres before the certified subdivision search.  The
short quartic eliminants and all accepted witnesses are shared with the
existing direct quadratic path; no convergence hypothesis is supplied. -/
@[expose] def fastRefinement? {parameter : Gaussian} {ambient : QuadraticBox}
    (current : WindingOneState
      (rootPolynomial parameter) ambient)
    (epsilon : Coordinate) (positive : 0 < epsilon) :
    Option (FastRefinement current epsilon) :=
  match Newton.Search.Attempt.attempt (SquareRoot.Clearance.QuadraticAxisElimination.quadraticAxisElimination parameter)
      current.raw epsilon
      (SquareRoot.Clearance.QuadraticLineClearance.Owner.quadraticAxisClearances parameter) with
  | some accepted => some
      { state := accepted.state
        nested := (Geometry.Rational.Box.Refinement.StrictInterior.refines accepted.strict)
        strict := accepted.strict
        accurate := accepted.accurate }
  | none => subdivisionRefinement? current epsilon positive

/-! A transported owner normally uses only its displayed initial state on the
next prepared edge.  Building `ShrinkingTrack.ofInitial` eagerly evaluates the
quadratic eliminant captured by its refinement closure, even when no
refinement is requested.  The following extensionally identical constructor
puts that finite computation inside the closure instead. -/

/-- Refine the original quadratic state using checked fast extraction with the original total Newton fallback.

A successful finite attempt supplies its actual strict, accurate state; otherwise the original squarefree quadratic
extractor supplies the same winding-one interface. -/
@[expose] def deferredRefine {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) {ambient : QuadraticBox}
    (current : WindingOneState
      (rootPolynomial parameter) ambient)
    (epsilon : Coordinate) (positive : 0 < epsilon) :
    WindingOneState
      (rootPolynomial parameter) ambient :=
  match fastRefinement? current epsilon positive with
  | some fast => fast.state
  | none =>
      Track.Newton.Refinement.refineState
        (by
          unfold rootPolynomial
          rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree]
          exact Riemann.RootContinuation.SquareRootDegree.degreeTwo_atLeastTwo)
        (by
          unfold rootPolynomial
          exact Power.Gaussian.Squarefree.squarefree parameterNonzero
            Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (SquareRoot.Clearance.QuadraticAxisElimination.quadraticAxisElimination parameter)
        current epsilon positive

/-- Every branch of deferred quadratic refinement stays inside the original state box. -/
theorem deferredRefine_refines {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) {ambient : QuadraticBox}
    (current : WindingOneState
      (rootPolynomial parameter) ambient)
    (epsilon : Coordinate) (positive : 0 < epsilon) :
    (deferredRefine parameterNonzero current epsilon
      positive).box.Refines
      current.box := by
  unfold deferredRefine
  generalize attempt : fastRefinement? current epsilon positive = result
  cases result with
  | none => exact Track.Newton.Refinement.refineState_refines _ _ _ _ _ _
  | some fast => exact fast.nested

/-- Every branch of deferred quadratic refinement lies strictly inside the original state box. -/
theorem deferredRefine_strict {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) {ambient : QuadraticBox}
    (current : WindingOneState
      (rootPolynomial parameter) ambient)
    (epsilon : Coordinate) (positive : 0 < epsilon) :
    (deferredRefine parameterNonzero current epsilon
      positive).box.StrictInterior
      current.box := by
  unfold deferredRefine
  generalize attempt : fastRefinement? current epsilon positive = result
  cases result with
  | none => exact Track.Newton.Refinement.refineState_strict _ _ _ _ _ _
  | some fast => exact fast.strict

/-- Every branch of deferred quadratic refinement meets the positive requested squared-diagonal accuracy. -/
theorem deferredRefine_accurate {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) {ambient : QuadraticBox}
    (current : WindingOneState
      (rootPolynomial parameter) ambient)
    (epsilon : Coordinate) (positive : 0 < epsilon) :
    (deferredRefine parameterNonzero current epsilon
      positive).box.diagonalSq ≤
      epsilon ^ 2 := by
  unfold deferredRefine
  generalize attempt : fastRefinement? current epsilon positive = result
  cases result with
  | none => exact Track.Newton.Refinement.refineState_accurate _ _ _ _ _ _
  | some fast => exact fast.accurate

/-- Extend the original quadratic state with the retained delayed refinement operation.

The track stores the actual initial state and its nested, strict and accurate refinement proofs without executing later
refinement requests. -/
@[expose] def deferredTrack {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) {ambient : QuadraticBox}
    (initial : WindingOneState
      (rootPolynomial parameter) ambient) :
    Track.Basic.WindingOneTrack
      (rootPolynomial parameter) ambient where
  initial := initial
  refine := deferredRefine parameterNonzero
  nested := deferredRefine_refines parameterNonzero
  strict := deferredRefine_strict parameterNonzero
  accurate := deferredRefine_accurate parameterNonzero

/-- Extend a displayed quadratic winding state without eagerly evaluating
the eliminant for later refinement.  In particular, a separately certified
same-box clearance can reuse the existing delayed refinement algorithm. -/
@[expose] def ownerOfState {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) {ambient : QuadraticBox}
    (initial : WindingOneState
      (rootPolynomial parameter) ambient) : Owner parameter
        where
  parameterNonzero := parameterNonzero
  ambient := ambient
  track := deferredTrack parameterNonzero initial

/-- Package an original quadratic child with its retained winding and four line clearances.

The child refines the source owner's initial box, which remains the ambient of the returned winding-one state. -/
@[expose] def childState {parameter : Gaussian} (source : Owner parameter)
    (child : QuadraticBox) (childRefines : child.Refines source.track.initial.box)
    (childProper : child.Proper)
    (clearance : BoundaryClearance
      (rootPolynomial parameter) child)
    (windingFour : Winding.Box.Basic.quadrupledBoxWinding
      (rootPolynomial parameter) child = 4)
    (left : VerticalLineClearance
      (rootPolynomial parameter) source.track.initial.box child.xLower)
    (right : VerticalLineClearance
      (rootPolynomial parameter) source.track.initial.box child.xUpper)
    (bottom : HorizontalLineClearance
      (rootPolynomial parameter) source.track.initial.box child.yLower)
    (top : HorizontalLineClearance
      (rootPolynomial parameter) source.track.initial.box child.yUpper) :
    WindingOneState
      (rootPolynomial parameter) source.track.initial.box where
  box := child
  refinesAmbient := childRefines
  proper := childProper
  clearance := clearance
  rawWindingFour := windingFour
  ambientLeftClearance := left
  ambientRightClearance := right
  ambientBottomClearance := bottom
  ambientTopClearance := top

/-- Construct a quadratic owner whose initial state uses the direct
resultant formula from the outset. -/
@[expose] def directOwnerOfBox (parameter : Gaussian) (parameterNonzero : parameter ≠ 0)
    (box : QuadraticBox) (proper : box.Proper)
    (leftNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter box.xLower ≠ 0)
    (rightNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter box.xUpper ≠ 0)
    (bottomNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter box.yLower ≠ 0)
    (topNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter box.yUpper ≠ 0)
    (windingFour : Winding.Box.Basic.quadrupledBoxWinding
      (rootPolynomial parameter) box = 4) : Owner parameter :=
  let clearance := directBoundaryClearance parameter box leftNonzero
    rightNonzero bottomNonzero topNonzero
  let initial : WindingOneState
      (rootPolynomial parameter) box :=
    { box := box
      refinesAmbient := Box.refines_refl box
      proper := proper
      clearance := clearance
      rawWindingFour := windingFour
      ambientLeftClearance := Clearance.Box.Boundary.Lines.leftOfBoundary clearance
      ambientRightClearance := Clearance.Box.Boundary.Lines.rightOfBoundary clearance
      ambientBottomClearance := Clearance.Box.Boundary.Lines.bottomOfBoundary clearance
      ambientTopClearance := Clearance.Box.Boundary.Lines.topOfBoundary clearance }
  { parameterNonzero := parameterNonzero
    ambient := box
    track := deferredTrack parameterNonzero initial }

/-- The direct quadratic owner retains exactly its supplied initial box. -/
@[simp] theorem directOwnerOfBox_initial_box
    (parameter : Gaussian) (parameterNonzero : parameter ≠ 0)
    (box : QuadraticBox) (proper : box.Proper)
    (leftNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter box.xLower ≠ 0)
    (rightNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter box.xUpper ≠ 0)
    (bottomNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter box.yLower ≠ 0)
    (topNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter box.yUpper ≠ 0)
    (windingFour : Winding.Box.Basic.quadrupledBoxWinding
      (rootPolynomial parameter) box = 4) :
    (directOwnerOfBox parameter parameterNonzero box proper leftNonzero
      rightNonzero bottomNonzero topNonzero windingFour).track.initial.box =
        box := rfl

/-- The direct quadratic owner uses exactly its supplied box as ambient. -/
@[simp] theorem directOwnerOfBox_ambient
    (parameter : Gaussian) (parameterNonzero : parameter ≠ 0)
    (box : QuadraticBox) (proper : box.Proper)
    (leftNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter box.xLower ≠ 0)
    (rightNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter box.xUpper ≠ 0)
    (bottomNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter box.yLower ≠ 0)
    (topNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter box.yUpper ≠ 0)
    (windingFour : Winding.Box.Basic.quadrupledBoxWinding
      (rootPolynomial parameter) box = 4) :
    (directOwnerOfBox parameter parameterNonzero box proper leftNonzero
      rightNonzero bottomNonzero topNonzero windingFour).ambient = box := rfl

/-- The direct quadratic owner retains exactly the four-resultant boundary-clearance bound. -/
@[simp] theorem directOwnerOfBox_initial_clearance_bound
    (parameter : Gaussian) (parameterNonzero : parameter ≠ 0)
    (box : QuadraticBox) (proper : box.Proper)
    (leftNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter box.xLower ≠ 0)
    (rightNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter box.xUpper ≠ 0)
    (bottomNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter box.yLower ≠ 0)
    (topNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter box.yUpper ≠ 0)
    (windingFour : Winding.Box.Basic.quadrupledBoxWinding
      (rootPolynomial parameter) box = 4) :
    (directOwnerOfBox parameter parameterNonzero box proper leftNonzero
      rightNonzero bottomNonzero topNonzero windingFour).track.initial.clearance.bound =
        (directBoundaryClearance parameter box leftNonzero rightNonzero
          bottomNonzero topNonzero).bound := rfl

/-- A directly presented quadratic owner stores the same boundary bound on
each ambient side. -/
theorem directOwnerOfBox_ambientClearanceDominance
    (parameter : Gaussian) (parameterNonzero : parameter ≠ 0)
    (box : QuadraticBox) (proper : box.Proper)
    (leftNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter box.xLower ≠ 0)
    (rightNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter box.xUpper ≠ 0)
    (bottomNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter box.yLower ≠ 0)
    (topNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter box.yUpper ≠ 0)
    (windingFour : Winding.Box.Basic.quadrupledBoxWinding
      (rootPolynomial parameter) box = 4) :
    AmbientClearanceDominance
      (directOwnerOfBox parameter parameterNonzero box proper leftNonzero
        rightNonzero bottomNonzero topNonzero windingFour) := by
  exact ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩

/-- Midpoint split using the quadratic side resultants directly, with no
Sylvester eliminant construction. -/
@[expose] def midpointGrid (parameter : Gaussian) (box : QuadraticBox)
    (proper : box.Proper)
    (verticalNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter (midpoint box.xLower box.xUpper) ≠ 0)
    (horizontalNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter (midpoint box.yLower box.yUpper) ≠ 0) :
    Clearance.Box.Grid.Four.Basic.ClearFourGrid (rootPolynomial parameter) box where
  xCut := midpoint box.xLower box.xUpper
  yCut := midpoint box.yLower box.yUpper
  xInside := ⟨(midpoint_strict proper.1).1.le,
    (midpoint_strict proper.1).2.le⟩
  yInside := ⟨(midpoint_strict proper.2).1.le,
    (midpoint_strict proper.2).2.le⟩
  verticalClearance := SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directVerticalClearance
    parameter box _ verticalNonzero
  horizontalClearance :=
    SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directHorizontalClearance parameter box _
      horizontalNonzero

/-- Retain the original lower endpoint of the left-shifted interval. -/
private def leftShiftLower (lower _upper : Coordinate) : Fraction.Rational :=
  lower

/-- The rational point seven eighths of the way from the original lower endpoint to the upper endpoint. -/
private def leftShiftUpper (lower upper : Coordinate) : Fraction.Rational :=
  midpoint (midpoint (midpoint
    lower upper) upper) upper

/-- The rational point one eighth of the way from the original lower endpoint to the upper endpoint. -/
private def rightShiftLower (lower upper : Coordinate) : Fraction.Rational :=
  midpoint lower (midpoint lower
    (midpoint lower upper))

/-- Retain the original upper endpoint of the right-shifted interval. -/
private def rightShiftUpper (_lower upper : Coordinate) : Fraction.Rational :=
  upper

/-- The left-shifted interval of strictly ordered endpoints is proper. -/
private theorem leftShift_proper {lower upper : Coordinate}
    (proper : lower < upper) :
    leftShiftLower lower upper < leftShiftUpper lower upper :=
      by
  exact (midpoint_strict proper).1.trans
    ((midpoint_strict (midpoint_strict proper).2).1.trans
      (midpoint_strict
        (midpoint_strict (midpoint_strict proper).2).2).1)

/-- The right-shifted interval of strictly ordered endpoints is proper. -/
private theorem rightShift_proper {lower upper : Coordinate}
    (proper : lower < upper) :
    rightShiftLower lower upper < rightShiftUpper lower upper
      := by
  exact
    ((midpoint_strict
      (midpoint_strict (midpoint_strict proper).1).1).2.trans
        (midpoint_strict (midpoint_strict proper).1).2).trans
      (midpoint_strict proper).2

/-- The retained left-shift lower endpoint is no larger than the original lower endpoint. -/
private theorem leftShiftLower_le {lower upper : Coordinate}
    (_valid : lower ≤ upper) : leftShiftLower lower upper ≤ lower := by
  exact le_rfl

/-- The original midpoint is no larger than the left-shift upper endpoint. -/
private theorem midpoint_le_leftShiftUpper {lower upper : Coordinate}
    (proper : lower < upper) : midpoint lower upper ≤
      leftShiftUpper lower upper := by
  exact ((midpoint_strict (midpoint_strict proper).2).1.trans
    (midpoint_strict
      (midpoint_strict (midpoint_strict proper).2).2).1).le

/-- The right-shift lower endpoint is no larger than the original midpoint. -/
private theorem rightShiftLower_le_midpoint {lower upper : Coordinate}
    (proper : lower < upper) : rightShiftLower lower upper ≤
      midpoint lower upper := by
  exact ((midpoint_strict
    (midpoint_strict (midpoint_strict proper).1).1).2.trans
      (midpoint_strict (midpoint_strict proper).1).2).le

/-- The retained right-shift upper endpoint is no smaller than the original upper endpoint. -/
private theorem upper_le_rightShiftUpper {lower upper : Coordinate}
    (_valid : lower ≤ upper) : upper ≤ rightShiftUpper lower upper := by
  exact le_rfl

/-- The left-shift upper endpoint is no larger than the original upper endpoint. -/
private theorem leftShiftUpper_le {lower upper : Coordinate}
    (proper : lower < upper) : leftShiftUpper lower upper ≤ upper := by
  exact (midpoint_strict
    (midpoint_strict (midpoint_strict proper).2).2).2.le

/-- The original lower endpoint is no larger than the right-shift lower endpoint. -/
private theorem lower_le_rightShiftLower {lower upper : Coordinate}
    (proper : lower < upper) : lower ≤ rightShiftLower lower upper := by
  exact (midpoint_strict
    (midpoint_strict (midpoint_strict proper).1).1).1.le

/-- The proper lower-left overlapping box retaining the lower seven eighths of each original coordinate interval. -/
private def shiftedLowerLeft (box : QuadraticBox) (proper : box.Proper) : QuadraticBox where
  xLower := leftShiftLower box.xLower box.xUpper
  xUpper := leftShiftUpper box.xLower box.xUpper
  yLower := leftShiftLower box.yLower box.yUpper
  yUpper := leftShiftUpper box.yLower box.yUpper
  x_valid := (leftShift_proper proper.1).le
  y_valid := (leftShift_proper proper.2).le

/-- The proper upper-left overlapping box retaining the lower horizontal and upper vertical seven-eighths intervals. -/
private def shiftedUpperLeft (box : QuadraticBox) (proper : box.Proper) : QuadraticBox where
  xLower := leftShiftLower box.xLower box.xUpper
  xUpper := leftShiftUpper box.xLower box.xUpper
  yLower := rightShiftLower box.yLower box.yUpper
  yUpper := rightShiftUpper box.yLower box.yUpper
  x_valid := (leftShift_proper proper.1).le
  y_valid := (rightShift_proper proper.2).le

/-- The proper lower-right overlapping box retaining the upper horizontal and lower vertical seven-eighths intervals. -/
private def shiftedLowerRight (box : QuadraticBox) (proper : box.Proper) : QuadraticBox where
  xLower := rightShiftLower box.xLower box.xUpper
  xUpper := rightShiftUpper box.xLower box.xUpper
  yLower := leftShiftLower box.yLower box.yUpper
  yUpper := leftShiftUpper box.yLower box.yUpper
  x_valid := (rightShift_proper proper.1).le
  y_valid := (leftShift_proper proper.2).le

/-- The proper upper-right overlapping box retaining the upper seven eighths of each original coordinate interval. -/
private def shiftedUpperRight (box : QuadraticBox) (proper : box.Proper) : QuadraticBox where
  xLower := rightShiftLower box.xLower box.xUpper
  xUpper := rightShiftUpper box.xLower box.xUpper
  yLower := rightShiftLower box.yLower box.yUpper
  yUpper := rightShiftUpper box.yLower box.yUpper
  x_valid := (rightShift_proper proper.1).le
  y_valid := (rightShift_proper proper.2).le

set_option genInjectivity false in
/-- A directly certified quadratic owner on the exact supplied rational box.

The record retains the deferred constructor identity, four nonzero resultants, box equalities and actual cached boundary
and ambient clearance values. -/
structure DirectBoxOwner (parameter : Gaussian) (box : QuadraticBox) where
  /-- The actual directly certified quadratic owner. -/ owner : Owner parameter
  /-- The retained owner equals the original deferred constructor on its own initial state. -/ deferred : owner =
    ownerOfState owner.parameterNonzero owner.track.initial
  /-- The retained owner's initial box equals the supplied box exactly. -/ initialBox : owner.track.initial.box = box
  /-- The retained owner's ambient equals the supplied box exactly. -/ ambientBox : owner.ambient = box
  /-- The retained owner's boundary bound controls every ambient-line bound. -/ dominance :
    AmbientClearanceDominance owner
  /-- The exact left side resultant of the retained quadratic box is nonzero. -/ leftNonzero :
    SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
      parameter box.xLower ≠ 0
  /-- The exact right side resultant of the retained quadratic box is nonzero. -/ rightNonzero :
    SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
      parameter box.xUpper ≠ 0
  /-- The exact bottom side resultant of the retained quadratic box is nonzero. -/ bottomNonzero :
    SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
      parameter box.yLower ≠ 0
  /-- The exact top side resultant of the retained quadratic box is nonzero. -/ topNonzero :
    SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
      parameter box.yUpper ≠ 0
  /-- The retained initial boundary bound equals the exact four-resultant minimum. -/ initialClearanceBound :
    owner.track.initial.clearance.bound =
    (directBoundaryClearance parameter box leftNonzero rightNonzero
      bottomNonzero topNonzero).bound
  /-- The retained left ambient bound equals that same four-resultant minimum. -/ ambientLeftClearanceBound :
    owner.track.initial.ambientLeftClearance.bound =
      (directBoundaryClearance parameter box leftNonzero rightNonzero
        bottomNonzero topNonzero).bound

constructive_injectivity DirectBoxOwner

/-- Check all four side resultants and winding four on the supplied proper quadratic box.

Success retains the actual direct owner and its defining box and clearance equalities; a failed finite check returns no
owner. -/
@[expose] def directOwnerOnBox? (parameter : Gaussian)
    (parameterNonzero : parameter ≠ 0) (box : QuadraticBox) (proper : box.Proper) :
    Option (DirectBoxOwner parameter box) :=
  if leftNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter box.xLower ≠ 0 then
    if rightNonzero :
        SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
          parameter box.xUpper ≠ 0 then
      if bottomNonzero :
          SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
            parameter box.yLower ≠ 0 then
        if topNonzero :
            SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
              parameter box.yUpper ≠ 0 then
          if windingFour : (Winding.Box.Basic.quadrupledBoxWinding
              (rootPolynomial parameter) box = 4) then
            some
              { owner := directOwnerOfBox parameter parameterNonzero box proper
                  leftNonzero rightNonzero bottomNonzero topNonzero windingFour
                deferred := rfl
                initialBox := directOwnerOfBox_initial_box parameter
                  parameterNonzero box proper leftNonzero rightNonzero
                    bottomNonzero topNonzero windingFour
                ambientBox := directOwnerOfBox_ambient parameter parameterNonzero
                  box proper leftNonzero rightNonzero bottomNonzero topNonzero
                    windingFour
                dominance := directOwnerOfBox_ambientClearanceDominance parameter
                  parameterNonzero box proper leftNonzero rightNonzero
                    bottomNonzero topNonzero windingFour
                leftNonzero := leftNonzero
                rightNonzero := rightNonzero
                bottomNonzero := bottomNonzero
                topNonzero := topNonzero
                initialClearanceBound :=
                  directOwnerOfBox_initial_clearance_bound parameter
                    parameterNonzero box proper leftNonzero rightNonzero
                      bottomNonzero topNonzero windingFour
                ambientLeftClearanceBound := rfl }
          else none
        else none
      else none
    else none
  else none

set_option genInjectivity false in
/-- A directly certified owner in one midpoint child of the parent box.

The original parameter and parent box identify the selected recentered box and the exact direct root owner supplied by
its retained certificates. -/
structure DirectRecenter (parameter : Gaussian) (parent : QuadraticBox) where
  /-- The actual directly certified recentered quadratic owner. -/ owner : Owner parameter
  /-- The recentered owner retains its original deferred constructor identity. -/ deferred : owner =
    ownerOfState owner.parameterNonzero owner.track.initial
  /-- The recentered initial box refines the original parent box. -/ refines : owner.track.initial.box.Refines parent

constructive_injectivity DirectRecenter

/-- Try the four midpoint children in fixed finite order and retain the unique
winding-four child as a freshly centred quadratic owner. -/
@[expose] def midpointRecenter? (parameter : Gaussian) (parameterNonzero : parameter ≠ 0)
    (box : QuadraticBox) (proper : box.Proper) :
    Option (DirectRecenter parameter box) := by
  let xCut := midpoint box.xLower box.xUpper
  let yCut := midpoint box.yLower box.yUpper
  if xNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter xCut ≠ 0 then
    if yNonzero :
        SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
          parameter yCut ≠ 0 then
      let grid := midpointGrid parameter box proper xNonzero yNonzero
      if lowerLeftWinding : (Winding.Box.Basic.quadrupledBoxWinding
          (rootPolynomial parameter) grid.lowerLeft = 4) then
        let candidate := grid.lowerLeft
        match directOwnerOnBox? parameter parameterNonzero candidate
            ⟨(midpoint_strict proper.1).1, (midpoint_strict
              proper.2).1⟩ with
        | none => exact none
        | some shifted =>
            exact some
              { owner := shifted.owner
                deferred := shifted.deferred
                refines := by
                  rw [shifted.initialBox]
                  exact grid.lowerLeft_refines }
      else if upperLeftWinding : (Winding.Box.Basic.quadrupledBoxWinding
          (rootPolynomial parameter) grid.upperLeft = 4) then
        let candidate := grid.upperLeft
        match directOwnerOnBox? parameter parameterNonzero candidate
            ⟨(midpoint_strict proper.1).1, (midpoint_strict
              proper.2).2⟩ with
        | none => exact none
        | some shifted =>
            exact some
              { owner := shifted.owner
                deferred := shifted.deferred
                refines := by
                  rw [shifted.initialBox]
                  exact grid.upperLeft_refines }
      else if lowerRightWinding : (Winding.Box.Basic.quadrupledBoxWinding
          (rootPolynomial parameter) grid.lowerRight = 4) then
        let candidate := grid.lowerRight
        match directOwnerOnBox? parameter parameterNonzero candidate
            ⟨(midpoint_strict proper.1).2, (midpoint_strict
              proper.2).1⟩ with
        | none => exact none
        | some shifted =>
            exact some
              { owner := shifted.owner
                deferred := shifted.deferred
                refines := by
                  rw [shifted.initialBox]
                  exact grid.lowerRight_refines }
      else if upperRightWinding : (Winding.Box.Basic.quadrupledBoxWinding
          (rootPolynomial parameter) grid.upperRight = 4) then
        let candidate := grid.upperRight
        match directOwnerOnBox? parameter parameterNonzero candidate
            ⟨(midpoint_strict proper.1).2, (midpoint_strict
              proper.2).2⟩ with
        | none => exact none
        | some shifted =>
            exact some
              { owner := shifted.owner
                deferred := shifted.deferred
                refines := by
                  rw [shifted.initialBox]
                  exact grid.upperRight_refines }
      else exact none
    else exact none
  else exact none

/-- The Gaussian point formed by the two original rational interval midpoints. -/
@[expose] def boxCenter (box : QuadraticBox) : Gaussian :=
  ⟨midpoint box.xLower box.xUpper, midpoint box.yLower box.yUpper⟩

/-- Move three quarters of the way from a source coordinate toward a selected
midpoint-child centre.  Since a child centre is one quarter-width from its
parent centre, this moves the replacement window by three sixteenths of the
source width, the largest dyadic move used here while retaining a strict
overlap margin around that child. -/
@[expose] def gentleCoordinate (source target : Coordinate) : Fraction.Rational :=
  midpoint target (midpoint source target)

/-- Move each source-box center coordinate three quarters toward the corresponding retained child center. -/
@[expose] def gentleCenter (source child : QuadraticBox) : Gaussian :=
  ⟨gentleCoordinate (boxCenter source).re (boxCenter
    child).re,
    gentleCoordinate (boxCenter source).im
      (boxCenter child).im⟩

set_option genInjectivity false in
/-- The executable, source-state-independent part of a moving reset.  Keeping
the selected candidate and its direct owner together lets explicit examples
evaluate the geometry from a cached box without reopening a transported
owner merely to rediscover that box.

The original parameter, source box and child index the selected candidate and its direct owner; strict child containment
concerns that exact cached candidate. -/
structure MovingCandidateData (parameter : Gaussian)
    (sourceBox child : QuadraticBox) where
  /-- The actual rational box selected by the original moving-window calculation. -/ candidate : QuadraticBox
  /-- The supplied original child lies strictly inside the retained candidate. -/ childStrict : child.StrictInterior
    candidate
  /-- The directly certified original quadratic owner on that exact candidate box. -/ moved :
    DirectBoxOwner parameter candidate

constructive_injectivity MovingCandidateData

/-- Check a same-width square centered toward the retained child for direct quadratic ownership.

Success retains the exact candidate, strict child containment and original direct-owner certificate; failure retains no
candidate owner. -/
@[expose] def movingCandidateData? (parameter : Gaussian)
    (parameterNonzero : parameter ≠ 0) (sourceBox : QuadraticBox)
    (sourceProper : sourceBox.Proper) (child : QuadraticBox) :
    Option (MovingCandidateData parameter sourceBox child) := by
  let radius := sourceBox.widthX / 2
  have radiusPositive : 0 < radius := by
    exact Fraction.Order.Field.div_pos_direct
      (Fraction.Order.Arithmetic.sub_pos_direct sourceProper.1) (by decide)
  let candidate := Box.Square.Centered.Affine.centeredSquare
    (gentleCenter sourceBox child) radius radiusPositive.le
  if childStrict : child.StrictInterior candidate then
    match directOwnerOnBox? parameter parameterNonzero candidate
        (Box.Square.Centered.centeredSquare_proper
          (gentleCenter sourceBox child) radiusPositive) with
    | none => exact none
    | some moved => exact some ⟨candidate, childStrict, moved⟩
  else exact none

/-- Box-only projection of one already selected moving candidate.  Exposing
this finite calculation separately lets generated examples cache the branch
choice and elaborate the candidate check independently. -/
@[expose] def movingCandidateBox? (parameter : Gaussian)
    (parameterNonzero : parameter ≠ 0) (sourceBox : QuadraticBox)
    (sourceProper : sourceBox.Proper) (child : QuadraticBox) : Option QuadraticBox :=
  Option.map MovingCandidateData.candidate
    (movingCandidateData? parameter parameterNonzero sourceBox sourceProper child)

set_option genInjectivity false in
/-- A quadratic owner whose box may move instead of remaining nested.  The
displayed bridge owner refines the source and is strictly inside the moved
owner; refining that bridge once supplies the common strict tail used by the
operational-equivalence proof without making path evaluation run the generic
refiner eagerly.

The selected moving recenter retains the same source owner and target parameter, with its cached box and exact
owner-construction readbacks. -/
structure MovingRecenter (parameter : Gaussian) (source : Owner parameter) where
  /-- The actual directly certified replacement owner. -/ owner : Owner parameter
  /-- The replacement retains its original deferred constructor identity. -/ deferred : owner =
    ownerOfState owner.parameterNonzero owner.track.initial
  /-- The directly certified box used to construct `owner`.  Retaining this
  value avoids transporting dependent boundary-clearance data merely to
  inspect its four executable side bounds. -/
  ownerBox : QuadraticBox
  /-- The replacement initial box equals the retained owner box exactly. -/ ownerInitialBox : owner.track.initial.box =
    ownerBox
  /-- The replacement ambient equals the retained owner box exactly. -/ ownerAmbientBox : owner.ambient = ownerBox
  /-- The replacement boundary bound controls its four ambient-line bounds. -/ ownerDominance :
    AmbientClearanceDominance owner
  /-- The original certified bridge owner connecting source and replacement. -/ bridgeOwner :
    Owner parameter
  /-- The retained bridge's initial box refines the original source box. -/ bridgeRefinesSource :
    bridgeOwner.track.initial.box.Refines
    source.track.initial.box
  /-- The retained bridge's initial box lies strictly inside the replacement box. -/ bridgeStrictOwner :
    bridgeOwner.track.initial.box.StrictInterior
    owner.track.initial.box
  /-- The exact left side resultant on the retained replacement box is nonzero. -/ ownerLeftNonzero :
    SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
      parameter ownerBox.xLower ≠ 0
  /-- The exact right side resultant on the retained replacement box is nonzero. -/ ownerRightNonzero :
    SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
      parameter ownerBox.xUpper ≠ 0
  /-- The exact bottom side resultant on the retained replacement box is nonzero. -/ ownerBottomNonzero :
    SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
      parameter ownerBox.yLower ≠ 0
  /-- The exact top side resultant on the retained replacement box is nonzero. -/ ownerTopNonzero :
    SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
      parameter ownerBox.yUpper ≠ 0
  /-- The replacement boundary bound equals its exact retained four-resultant clearance. -/ ownerDirectClearanceBound :
    owner.track.initial.clearance.bound =
    (directBoundaryClearance parameter ownerBox
      ownerLeftNonzero ownerRightNonzero ownerBottomNonzero
        ownerTopNonzero).bound
  /-- The replacement left ambient bound equals its exact retained four-resultant clearance. -/
    ownerAmbientLeftClearanceBound :
    owner.track.initial.ambientLeftClearance.bound =
      (directBoundaryClearance parameter ownerBox
        ownerLeftNonzero ownerRightNonzero ownerBottomNonzero
          ownerTopNonzero).bound

constructive_injectivity MovingRecenter

/-- Attach the supplied bridge owner to the actual checked moving candidate.

The retained bridge refines the original source and lies strictly inside the selected replacement box, preserving both
input owners. -/
@[expose] def movingCandidate? {parameter : Gaussian} (source : Owner parameter)
    (child : QuadraticBox) (childRefines : child.Refines source.track.initial.box)
    (bridgeOwner : Owner parameter)
    (bridgeBox : bridgeOwner.track.initial.box = child) :
    Option (MovingRecenter parameter source) := by
  match movingCandidateData? parameter source.parameterNonzero
      source.track.initial.box source.track.initial.proper child with
    | none => exact none
    | some data =>
        exact some
          { owner := data.moved.owner
            deferred := data.moved.deferred
            ownerBox := data.candidate
            ownerInitialBox := data.moved.initialBox
            ownerAmbientBox := data.moved.ambientBox
            ownerDominance := data.moved.dominance
            bridgeOwner := bridgeOwner
            bridgeRefinesSource := by
              rw [bridgeBox]
              exact childRefines
            bridgeStrictOwner := by
              rw [bridgeBox, data.moved.initialBox]
              exact data.childStrict
            ownerLeftNonzero := data.moved.leftNonzero
            ownerRightNonzero := data.moved.rightNonzero
            ownerBottomNonzero := data.moved.bottomNonzero
            ownerTopNonzero := data.moved.topNonzero
            ownerDirectClearanceBound := data.moved.initialClearanceBound
            ownerAmbientLeftClearanceBound :=
              data.moved.ambientLeftClearanceBound }

/-- Move a quadratic continuation window gently toward an overlapping
midpoint child.  The replacement keeps the source width, is independently
checked for winding four, and carries a bridge that witnesses the same root. -/
@[expose] def movingRecenter? {parameter : Gaussian} (source : Owner parameter) :
    Option (MovingRecenter parameter source) := by
  let box := source.track.initial.box
  let proper := source.track.initial.proper
  let xCut := midpoint box.xLower box.xUpper
  let yCut := midpoint box.yLower box.yUpper
  if xNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter xCut ≠ 0 then
    if yNonzero :
        SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
          parameter yCut ≠ 0 then
      let grid := midpointGrid parameter box proper xNonzero yNonzero
      if lowerLeftWinding : (Winding.Box.Basic.quadrupledBoxWinding
          (rootPolynomial parameter) grid.lowerLeft = 4) then
        let childClearances :=
          grid.childClearances source.track.initial.clearance
        let bridgeState := childState source grid.lowerLeft
          grid.lowerLeft_refines
          ⟨(midpoint_strict proper.1).1, (midpoint_strict
            proper.2).1⟩
          childClearances.1 lowerLeftWinding
          (Clearance.Box.Boundary.Lines.leftOfBoundary source.track.initial.clearance)
          grid.verticalClearance
          (Clearance.Box.Boundary.Lines.bottomOfBoundary source.track.initial.clearance)
          grid.horizontalClearance
        let bridgeOwner := ownerOfState source.parameterNonzero bridgeState
        exact movingCandidate? source grid.lowerLeft grid.lowerLeft_refines
          bridgeOwner rfl
      else if upperLeftWinding : (Winding.Box.Basic.quadrupledBoxWinding
          (rootPolynomial parameter) grid.upperLeft = 4) then
        let childClearances :=
          grid.childClearances source.track.initial.clearance
        let bridgeState := childState source grid.upperLeft
          grid.upperLeft_refines
          ⟨(midpoint_strict proper.1).1, (midpoint_strict
            proper.2).2⟩
          childClearances.2.1 upperLeftWinding
          (Clearance.Box.Boundary.Lines.leftOfBoundary source.track.initial.clearance)
          grid.verticalClearance grid.horizontalClearance
          (Clearance.Box.Boundary.Lines.topOfBoundary source.track.initial.clearance)
        let bridgeOwner := ownerOfState source.parameterNonzero bridgeState
        exact movingCandidate? source grid.upperLeft grid.upperLeft_refines
          bridgeOwner rfl
      else if lowerRightWinding : (Winding.Box.Basic.quadrupledBoxWinding
          (rootPolynomial parameter) grid.lowerRight = 4) then
        let childClearances :=
          grid.childClearances source.track.initial.clearance
        let bridgeState := childState source grid.lowerRight
          grid.lowerRight_refines
          ⟨(midpoint_strict proper.1).2, (midpoint_strict
            proper.2).1⟩
          childClearances.2.2.1 lowerRightWinding grid.verticalClearance
          (Clearance.Box.Boundary.Lines.rightOfBoundary source.track.initial.clearance)
          (Clearance.Box.Boundary.Lines.bottomOfBoundary source.track.initial.clearance)
          grid.horizontalClearance
        let bridgeOwner := ownerOfState source.parameterNonzero bridgeState
        exact movingCandidate? source grid.lowerRight grid.lowerRight_refines
          bridgeOwner rfl
      else if upperRightWinding : (Winding.Box.Basic.quadrupledBoxWinding
          (rootPolynomial parameter) grid.upperRight = 4) then
        let childClearances :=
          grid.childClearances source.track.initial.clearance
        let bridgeState := childState source grid.upperRight
          grid.upperRight_refines
          ⟨(midpoint_strict proper.1).2, (midpoint_strict
            proper.2).2⟩
          childClearances.2.2.2 upperRightWinding grid.verticalClearance
          (Clearance.Box.Boundary.Lines.rightOfBoundary source.track.initial.clearance)
          grid.horizontalClearance
          (Clearance.Box.Boundary.Lines.topOfBoundary source.track.initial.clearance)
        let bridgeOwner := ownerOfState source.parameterNonzero bridgeState
        exact movingCandidate? source grid.upperRight grid.upperRight_refines
          bridgeOwner rfl
      else exact none
    else exact none
  else exact none

/-- Box-only projection of `movingRecenter?`.  Its branch decisions and
candidate checks are identical, but it consumes an already cached source box
and properness proof instead of reducing an entire transported owner. -/
@[expose] def movingRecenterBox? (parameter : Gaussian) (parameterNonzero : parameter ≠ 0)
    (box : QuadraticBox) (proper : box.Proper) : Option QuadraticBox := by
  let xCut := midpoint box.xLower box.xUpper
  let yCut := midpoint box.yLower box.yUpper
  if xNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter xCut ≠ 0 then
    if yNonzero :
        SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
          parameter yCut ≠ 0 then
      let grid := midpointGrid parameter box proper xNonzero yNonzero
      if lowerLeftWinding : (Winding.Box.Basic.quadrupledBoxWinding
          (rootPolynomial parameter) grid.lowerLeft = 4) then
        exact movingCandidateBox? parameter parameterNonzero box proper
          grid.lowerLeft
      else if upperLeftWinding : (Winding.Box.Basic.quadrupledBoxWinding
          (rootPolynomial parameter) grid.upperLeft = 4) then
        exact movingCandidateBox? parameter parameterNonzero box proper
          grid.upperLeft
      else if lowerRightWinding : (Winding.Box.Basic.quadrupledBoxWinding
          (rootPolynomial parameter) grid.lowerRight = 4) then
        exact movingCandidateBox? parameter parameterNonzero box proper
          grid.lowerRight
      else if upperRightWinding : (Winding.Box.Basic.quadrupledBoxWinding
          (rootPolynomial parameter) grid.upperRight = 4) then
        exact movingCandidateBox? parameter parameterNonzero box proper
          grid.upperRight
      else exact none
    else exact none
  else exact none

/-- Replay a cached lower-left branch of the box-only moving search. -/
theorem movingRecenterBox?_eq_some_of_lowerLeft
    (parameter : Gaussian) (parameterNonzero : parameter ≠ 0)
    (box : QuadraticBox) (proper : box.Proper) (target : QuadraticBox)
    (xNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter (midpoint box.xLower box.xUpper) ≠ 0)
    (yNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter (midpoint box.yLower box.yUpper) ≠ 0)
    (lowerLeftWinding : Winding.Box.Basic.quadrupledBoxWinding
      (rootPolynomial parameter)
        (midpointGrid parameter box proper xNonzero yNonzero).lowerLeft = 4)
    (candidate : movingCandidateBox? parameter parameterNonzero box proper
      (midpointGrid parameter box proper xNonzero yNonzero).lowerLeft =
        some target) :
    movingRecenterBox? parameter parameterNonzero box proper = some target := by
  unfold movingRecenterBox?
  rw [dif_pos xNonzero, dif_pos yNonzero, dif_pos lowerLeftWinding]
  exact candidate

/-- Replay a cached upper-left branch of the box-only moving search. -/
theorem movingRecenterBox?_eq_some_of_upperLeft
    (parameter : Gaussian) (parameterNonzero : parameter ≠ 0)
    (box : QuadraticBox) (proper : box.Proper) (target : QuadraticBox)
    (xNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter (midpoint box.xLower box.xUpper) ≠ 0)
    (yNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter (midpoint box.yLower box.yUpper) ≠ 0)
    (lowerLeftWinding : Winding.Box.Basic.quadrupledBoxWinding
      (rootPolynomial parameter)
        (midpointGrid parameter box proper xNonzero yNonzero).lowerLeft ≠ 4)
    (upperLeftWinding : Winding.Box.Basic.quadrupledBoxWinding
      (rootPolynomial parameter)
        (midpointGrid parameter box proper xNonzero yNonzero).upperLeft = 4)
    (candidate : movingCandidateBox? parameter parameterNonzero box proper
      (midpointGrid parameter box proper xNonzero yNonzero).upperLeft =
        some target) :
    movingRecenterBox? parameter parameterNonzero box proper = some target := by
  unfold movingRecenterBox?
  rw [dif_pos xNonzero, dif_pos yNonzero, dif_neg lowerLeftWinding,
    dif_pos upperLeftWinding]
  exact candidate

/-- The full moving-candidate construction and its data-only projection retain exactly the same selected box. -/
private theorem movingCandidate_ownerBox_map {parameter : Gaussian}
    (source : Owner parameter) (child : QuadraticBox)
    (childRefines : child.Refines source.track.initial.box)
    (bridgeOwner : Owner parameter)
    (bridgeBox : bridgeOwner.track.initial.box = child) :
    Option.map (fun reset => reset.ownerBox)
        (movingCandidate? source child childRefines bridgeOwner bridgeBox) =
      Option.map MovingCandidateData.candidate
        (movingCandidateData? parameter source.parameterNonzero
          source.track.initial.box source.track.initial.proper child) := by
  unfold movingCandidate?
  generalize found : movingCandidateData? parameter source.parameterNonzero
    source.track.initial.box source.track.initial.proper child = result
  cases result <;> rfl

/-- The full reset and its box-only cached projection make exactly the same
finite branch choices. -/
theorem movingRecenter_ownerBox_map {parameter : Gaussian}
    (source : Owner parameter) :
    Option.map (fun reset => reset.ownerBox) (movingRecenter? source) =
      movingRecenterBox? parameter source.parameterNonzero
        source.track.initial.box source.track.initial.proper := by
  unfold movingRecenter? movingRecenterBox?
  dsimp only
  split
  · split
    · split
      · exact movingCandidate_ownerBox_map _ _ _ _ _
      · split
        · exact movingCandidate_ownerBox_map _ _ _ _ _
        · split
          · exact movingCandidate_ownerBox_map _ _ _ _ _
          · split
            · exact movingCandidate_ownerBox_map _ _ _ _ _
            · rfl
    · rfl
  · rfl

/-- Replace the source box in the cached projection by any propositionally
equal stored box.  The properness witness is proof-only. -/
theorem movingRecenter_ownerBox_map_of_box {parameter : Gaussian}
    (source : Owner parameter) (box : QuadraticBox) (proper : box.Proper)
    (boxEq : source.track.initial.box = box) :
    Option.map (fun reset => reset.ownerBox) (movingRecenter? source) =
      movingRecenterBox? parameter source.parameterNonzero box proper := by
  subst box
  exact movingRecenter_ownerBox_map source

/-- The original resultant-based same-box transport, retained as the total
fallback when the cheaper transported ambient clearances do not all carry the
requested move. -/
@[expose] def resultantReservedTransport {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.clearance.bound) (reserve : Coordinate) :
    Owner target :=
  let box := owner.track.initial.box
  let carried := Riemann.RootContinuation.SquareRootContinuation.transportedOwner
    owner.track.initial small
  if leftNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        target box.xLower ≠ 0 then
    if rightNonzero :
        SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
          target box.xUpper ≠ 0 then
      if bottomNonzero :
          SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
            target box.yLower ≠ 0 then
        if topNonzero :
            SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
              target box.yUpper ≠ 0 then
          if _reserveSmall : reserve <
              (directBoundaryClearance target box leftNonzero rightNonzero
                bottomNonzero topNonzero).bound then
            directOwnerOfBox target targetNonzero box carried.proper leftNonzero
              rightNonzero bottomNonzero topNonzero carried.rawWindingFour
          else
            match midpointRecenter? target targetNonzero box carried.proper
                with
            | some recentered => recentered.owner
            | none => owner.advance targetNonzero small
        else owner.advance targetNonzero small
      else owner.advance targetNonzero small
    else owner.advance targetNonzero small
  else owner.advance targetNonzero small

/-- Reserved transport stays on the source box or uses a strict generic
descendant, so its initial box always refines the source box. -/
private theorem resultantReservedTransport_initial_box_refines
    {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.clearance.bound) (reserve : Coordinate) :
    (resultantReservedTransport owner targetNonzero small
      reserve).track.initial.box.Refines
      owner.track.initial.box := by
  unfold resultantReservedTransport
  dsimp only
  by_cases leftNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        target owner.track.initial.box.xLower ≠ 0
  · rw [dif_pos leftNonzero]
    by_cases rightNonzero :
        SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
          target owner.track.initial.box.xUpper ≠ 0
    · rw [dif_pos rightNonzero]
      by_cases bottomNonzero :
          SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
            target owner.track.initial.box.yLower ≠ 0
      · rw [dif_pos bottomNonzero]
        by_cases topNonzero :
            SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
              target owner.track.initial.box.yUpper ≠ 0
        · rw [dif_pos topNonzero]
          by_cases reserveSmall : reserve <
              (directBoundaryClearance target owner.track.initial.box
                leftNonzero rightNonzero bottomNonzero topNonzero).bound
          · rw [dif_pos reserveSmall, directOwnerOfBox_initial_box]
            exact Box.refines_refl _
          · rw [dif_neg reserveSmall]
            generalize recenteredEq : midpointRecenter? target targetNonzero
              owner.track.initial.box
              (Riemann.RootContinuation.SquareRootContinuation.transportedOwner
                owner.track.initial small).proper = recentered
            cases recentered with
            | none =>
                change (owner.advance targetNonzero small).track.initial.box.Refines
                  owner.track.initial.box
                exact owner.advance_initial_box_refines targetNonzero small
            | some centered =>
                simp only
                exact centered.refines
        · rw [dif_neg topNonzero]
          exact owner.advance_initial_box_refines targetNonzero small
      · rw [dif_neg bottomNonzero]
        exact owner.advance_initial_box_refines targetNonzero small
    · rw [dif_neg rightNonzero]
      exact owner.advance_initial_box_refines targetNonzero small
  · rw [dif_neg leftNonzero]
    exact owner.advance_initial_box_refines targetNonzero small

set_option genInjectivity false in
/-- Structural data showing that a direct or recentered result remains in a
same-occurrence target owner on the transported parent box.

The original source and target owners remain separate; the retained relation identifies the actual direct presentation
and original clearance-bounded move. -/
structure DirectPresentationRelation {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.clearance.bound)
    (result : Owner target) where
  /-- The retained target owner serving as the common parent for the two presentations. -/ parent :
    Owner target
  /-- The actual generic continuation box lies strictly inside this retained parent. -/ genericStrictParent :
    (owner.advance targetNonzero small).track.initial.box.StrictInterior
      parent.track.initial.box
  /-- The actual direct or recentered result box refines the same retained parent. -/ resultRefinesParent :
    result.track.initial.box.Refines parent.track.initial.box

constructive_injectivity DirectPresentationRelation

/-- Computational branch data for reserved transport. -/
@[expose] def resultantReservedTransport_generic_relation
    {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.clearance.bound) (reserve : Coordinate) :
    PSum
      (resultantReservedTransport owner targetNonzero small reserve =
        owner.advance targetNonzero small)
      (DirectPresentationRelation owner targetNonzero small
        (resultantReservedTransport owner targetNonzero small reserve)) := by
  unfold resultantReservedTransport
  dsimp only
  by_cases leftNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        target owner.track.initial.box.xLower ≠ 0
  · rw [dif_pos leftNonzero]
    by_cases rightNonzero :
        SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
          target owner.track.initial.box.xUpper ≠ 0
    · rw [dif_pos rightNonzero]
      by_cases bottomNonzero :
          SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
            target owner.track.initial.box.yLower ≠ 0
      · rw [dif_pos bottomNonzero]
        by_cases topNonzero :
            SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
              target owner.track.initial.box.yUpper ≠ 0
        · rw [dif_pos topNonzero]
          by_cases reserveSmall : reserve <
              (directBoundaryClearance target owner.track.initial.box
                leftNonzero rightNonzero bottomNonzero topNonzero).bound
          · rw [dif_pos reserveSmall]
            exact PSum.inr
              { parent := directOwnerOfBox target targetNonzero
                  owner.track.initial.box
                  (Riemann.RootContinuation.SquareRootContinuation.transportedOwner
                    owner.track.initial small).proper
                  leftNonzero rightNonzero bottomNonzero topNonzero
                  (Riemann.RootContinuation.SquareRootContinuation.transportedOwner
                    owner.track.initial small).rawWindingFour
                genericStrictParent := by
                  change (owner.advance targetNonzero small).track.initial.box
                    |>.StrictInterior owner.track.initial.box
                  exact Riemann.RootContinuation.SquareRootContinuation.continuedTrack_initial_strict_source
                    targetNonzero owner.track.initial small
                resultRefinesParent := by
                  change owner.track.initial.box.Refines owner.track.initial.box
                  exact Box.refines_refl _ }
          · rw [dif_neg reserveSmall]
            generalize recenteredEq : midpointRecenter? target targetNonzero
              owner.track.initial.box
              (Riemann.RootContinuation.SquareRootContinuation.transportedOwner
                owner.track.initial small).proper = recentered
            cases recentered with
            | none =>
                change PSum
                  (owner.advance targetNonzero small =
                    owner.advance targetNonzero small)
                  (DirectPresentationRelation owner targetNonzero small
                    (owner.advance targetNonzero small))
                exact PSum.inl rfl
            | some centered =>
                simp only
                exact PSum.inr
                  { parent := directOwnerOfBox target targetNonzero
                      owner.track.initial.box
                      (Riemann.RootContinuation.SquareRootContinuation.transportedOwner
                        owner.track.initial small).proper
                      leftNonzero rightNonzero bottomNonzero topNonzero
                      (Riemann.RootContinuation.SquareRootContinuation.transportedOwner
                        owner.track.initial small).rawWindingFour
                    genericStrictParent := by
                      change
                        (owner.advance targetNonzero small).track.initial.box
                          |>.StrictInterior owner.track.initial.box
                      exact Riemann.RootContinuation.SquareRootContinuation.continuedTrack_initial_strict_source
                        targetNonzero owner.track.initial small
                    resultRefinesParent := centered.refines }
        · rw [dif_neg topNonzero]
          exact PSum.inl rfl
      · rw [dif_neg bottomNonzero]
        exact PSum.inl rfl
    · rw [dif_neg rightNonzero]
      exact PSum.inl rfl
  · rw [dif_neg leftNonzero]
    exact PSum.inl rfl

/-- Transport the source owner's left ambient-line clearance to a target
quadratic parameter. -/
@[expose] def ambientLeftAfterMove {source target : Gaussian}
    (owner : Owner source)
    (leftSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientLeftClearance.bound) :=
  Power.Clearance.Box.Transport.verticalClearanceAfterMove
    (target := target) Riemann.RootContinuation.SquareRootDegree.degreeTwo
      owner.track.initial.ambientLeftClearance leftSmall

/-- A transported left-side clearance is bounded by one quarter of the
square of its source bound.  This inexpensive upper estimate is useful to
cache branch decisions after a successful ambient Rouché transport.

The original transported left-boundary certificate retains the smaller positive bound; its selected minimum is bounded
by the displayed quarter-square threshold. -/
theorem ambientLeftAfterMove_bound_le_quarter_sq
    {source target : Gaussian} (owner : Owner source)
    (leftSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientLeftClearance.bound) :
    (ambientLeftAfterMove owner leftSmall).bound ≤
      owner.track.initial.ambientLeftClearance.bound ^ 2 / 4 := by
  rw [ambientLeftAfterMove,
    Power.Clearance.Box.Transport.verticalClearanceAfterMove_bound]
  let displacement :=
    Data.Gaussian.Norm.Basic.normSq (source - target)
  let clearance := owner.track.initial.ambientLeftClearance.bound
  let majorant := max 1
    (Dense.Rational.Bounds.Horner.evalSqBound
        (Dense.Gaussian.Path.Components.pathReal
          (Purelib.Polynomial.Power.Gaussian.rootPolynomial source
            Riemann.RootContinuation.SquareRootDegree.degreeTwo)
          (Gaussian.Cast.Winding.verticalBase owner.track.initial.box.xLower)
          Gaussian.Constants.imaginaryUnit)
        (Box.Intervals.verticalInterval owner.ambient) +
      Dense.Rational.Bounds.Horner.evalSqBound
        (Dense.Gaussian.Path.Components.pathImag
          (Purelib.Polynomial.Power.Gaussian.rootPolynomial source
            Riemann.RootContinuation.SquareRootDegree.degreeTwo)
          (Gaussian.Cast.Winding.verticalBase owner.track.initial.box.xLower)
          Gaussian.Constants.imaginaryUnit)
        (Box.Intervals.verticalInterval owner.ambient))
  have displacementNonnegative : 0 ≤ displacement :=
    Gaussian.Norm.Basic.normSq_nonneg _
  have marginNonnegative : 0 ≤ clearance - displacement :=
    Fraction.Order.Arithmetic.sub_nonneg_direct leftSmall.le
  have marginLe : clearance - displacement ≤ clearance := by
    calc
      clearance - displacement ≤ clearance - 0 :=
        Fraction.Order.Arithmetic.sub_le_sub_left_direct
          displacementNonnegative clearance
      _ = clearance := by ring1
  have squareLe : (clearance - displacement) ^ 2 ≤ clearance ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct marginNonnegative marginLe 2
  have denominatorLe : (4 : Coordinate) ≤ 4 * majorant := by
    calc
      (4 : Coordinate) = 4 * 1 := by ring1
      _ ≤ 4 * majorant :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Basic.le_max_left _ _) (by decide)
  calc
    (clearance - displacement) ^ 2 / (4 * majorant) ≤
        (clearance - displacement) ^ 2 / 4 :=
      Fraction.Order.Field.div_le_div_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.sq_nonneg_direct
          (clearance - displacement)) (by decide) denominatorLe
    _ ≤ clearance ^ 2 / 4 := by
      change (clearance - displacement) ^ 2 * (4 : Coordinate)⁻¹ ≤
        clearance ^ 2 * (4 : Coordinate)⁻¹
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        squareLe
        (Fraction.Order.Field.inv_pos_direct (by decide)).le

/-- Transport the source owner's right ambient-line clearance. -/
@[expose] def ambientRightAfterMove {source target : Gaussian}
    (owner : Owner source)
    (rightSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientRightClearance.bound) :=
  Power.Clearance.Box.Transport.verticalClearanceAfterMove
    (target := target) Riemann.RootContinuation.SquareRootDegree.degreeTwo
      owner.track.initial.ambientRightClearance rightSmall

/-- Transport the source owner's bottom ambient-line clearance. -/
@[expose] def ambientBottomAfterMove {source target : Gaussian}
    (owner : Owner source)
    (bottomSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientBottomClearance.bound) :=
  Power.Clearance.Box.Transport.horizontalClearanceAfterMove
    (target := target) Riemann.RootContinuation.SquareRootDegree.degreeTwo
      owner.track.initial.ambientBottomClearance bottomSmall

/-- Transport the source owner's top ambient-line clearance. -/
@[expose] def ambientTopAfterMove {source target : Gaussian}
    (owner : Owner source)
    (topSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientTopClearance.bound) :=
  Power.Clearance.Box.Transport.horizontalClearanceAfterMove
    (target := target) Riemann.RootContinuation.SquareRootDegree.degreeTwo
      owner.track.initial.ambientTopClearance topSmall

/-- Assemble the transported boundary clearance from the four transported
ambient-line certificates restricted to the displayed owner box. -/
@[expose] def ambientAfterMoveClearance {source target : Gaussian}
    (owner : Owner source)
    (leftSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientLeftClearance.bound)
    (rightSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientRightClearance.bound)
    (bottomSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientBottomClearance.bound)
    (topSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientTopClearance.bound) :
    BoundaryClearance (rootPolynomial target)
      owner.track.initial.box :=
  Clearance.Box.Boundary.Lines.boundaryOfLines
    ((ambientLeftAfterMove owner leftSmall).restrict
      owner.track.initial.refinesAmbient)
    ((ambientRightAfterMove owner rightSmall).restrict
      owner.track.initial.refinesAmbient)
    ((ambientBottomAfterMove owner bottomSmall).restrict
      owner.track.initial.refinesAmbient)
    ((ambientTopAfterMove owner topSmall).restrict
      owner.track.initial.refinesAmbient)

/-- The cached rational calculation underlying ambient Rouché transport. -/
@[simp] theorem ambientAfterMoveClearance_bound {source target : Gaussian}
    (owner : Owner source)
    (leftSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientLeftClearance.bound)
    (rightSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientRightClearance.bound)
    (bottomSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientBottomClearance.bound)
    (topSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientTopClearance.bound) :
    (ambientAfterMoveClearance owner leftSmall rightSmall bottomSmall
        topSmall).bound =
      min (ambientLeftAfterMove owner leftSmall).bound
        (min (ambientRightAfterMove owner rightSmall).bound
          (min (ambientBottomAfterMove owner bottomSmall).bound
            (ambientTopAfterMove owner topSmall).bound)) := by
  unfold ambientAfterMoveClearance
  rw [Clearance.Box.Boundary.Lines.boundaryOfLines_bound,
    VerticalLineClearance.restrict_bound,
    VerticalLineClearance.restrict_bound,
    HorizontalLineClearance.restrict_bound,
    HorizontalLineClearance.restrict_bound]

/-- The transported initial state, with its boundary clearance assembled from
the same four ambient-line transports retained in the state. -/
@[expose] def ambientRoucheState {source target : Gaussian}
    (owner : Owner source) (_targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.clearance.bound)
    (leftSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientLeftClearance.bound)
    (rightSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientRightClearance.bound)
    (bottomSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientBottomClearance.bound)
    (topSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientTopClearance.bound) :
    WindingOneState (rootPolynomial target) owner.ambient := by
  let carried := Riemann.RootContinuation.SquareRootContinuation.transportedOwner
    owner.track.initial small
  exact
    { box := owner.track.initial.box
      refinesAmbient := owner.track.initial.refinesAmbient
      proper := carried.proper
      clearance := ambientAfterMoveClearance owner leftSmall rightSmall
        bottomSmall topSmall
      rawWindingFour := carried.rawWindingFour
      ambientLeftClearance := ambientLeftAfterMove owner leftSmall
      ambientRightClearance := ambientRightAfterMove owner rightSmall
      ambientBottomClearance := ambientBottomAfterMove owner bottomSmall
      ambientTopClearance := ambientTopAfterMove owner topSmall }

/-- Carry the complete source state by the already available constant-term
Rouché estimates.  Unlike the resultant fallback, this only subtracts the
displayed squared displacement from five rational clearance bounds. -/
@[expose] def ambientRoucheTransport {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.clearance.bound)
    (leftSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientLeftClearance.bound)
    (rightSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientRightClearance.bound)
    (bottomSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientBottomClearance.bound)
    (topSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientTopClearance.bound) : Owner target :=
  ownerOfState targetNonzero
    (ambientRoucheState owner targetNonzero small leftSmall rightSmall
      bottomSmall topSmall)

/-- Ambient Rouché transport keeps the original owner's initial box exactly. -/
theorem ambientRoucheTransport_initial_box {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.clearance.bound)
    (leftSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientLeftClearance.bound)
    (rightSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientRightClearance.bound)
    (bottomSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientBottomClearance.bound)
    (topSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientTopClearance.bound) :
    (ambientRoucheTransport owner targetNonzero small leftSmall rightSmall
      bottomSmall topSmall).track.initial.box = owner.track.initial.box := rfl

/-- Ambient Rouché transport keeps the original owner's ambient box exactly. -/
private theorem ambientRoucheTransport_ambient {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.clearance.bound)
    (leftSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientLeftClearance.bound)
    (rightSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientRightClearance.bound)
    (bottomSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientBottomClearance.bound)
    (topSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientTopClearance.bound) :
    (ambientRoucheTransport owner targetNonzero small leftSmall rightSmall
      bottomSmall topSmall).ambient = owner.ambient := rfl

/-- The transported boundary-clearance minimum is no larger than the retained left ambient-line bound. -/
private theorem ambientAfterMoveClearance_le_left
    {source target : Gaussian} (owner : Owner source)
    (leftSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientLeftClearance.bound)
    (rightSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientRightClearance.bound)
    (bottomSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientBottomClearance.bound)
    (topSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientTopClearance.bound) :
    (ambientAfterMoveClearance owner leftSmall rightSmall bottomSmall
      topSmall).bound <= (ambientLeftAfterMove owner leftSmall).bound := by
  let left := ambientLeftAfterMove owner leftSmall
  let right := ambientRightAfterMove owner rightSmall
  let bottom := ambientBottomAfterMove owner bottomSmall
  let top := ambientTopAfterMove owner topSmall
  let refines := owner.track.initial.refinesAmbient
  calc
    (ambientAfterMoveClearance owner leftSmall rightSmall bottomSmall
        topSmall).bound =
        (Clearance.Box.Boundary.Lines.boundaryOfLines (left.restrict refines)
          (right.restrict refines) (bottom.restrict refines)
          (top.restrict refines)).bound := rfl
    _ <= (left.restrict refines).bound :=
      Clearance.Box.Boundary.Lines.boundaryOfLines_bound_le_left _ _ _ _
    _ = left.bound := VerticalLineClearance.restrict_bound _ _

/-- The transported boundary-clearance minimum is no larger than the retained right ambient-line bound. -/
private theorem ambientAfterMoveClearance_le_right
    {source target : Gaussian} (owner : Owner source)
    (leftSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientLeftClearance.bound)
    (rightSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientRightClearance.bound)
    (bottomSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientBottomClearance.bound)
    (topSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientTopClearance.bound) :
    (ambientAfterMoveClearance owner leftSmall rightSmall bottomSmall
      topSmall).bound <= (ambientRightAfterMove owner rightSmall).bound := by
  let left := ambientLeftAfterMove owner leftSmall
  let right := ambientRightAfterMove owner rightSmall
  let bottom := ambientBottomAfterMove owner bottomSmall
  let top := ambientTopAfterMove owner topSmall
  let refines := owner.track.initial.refinesAmbient
  calc
    (ambientAfterMoveClearance owner leftSmall rightSmall bottomSmall
        topSmall).bound =
        (Clearance.Box.Boundary.Lines.boundaryOfLines (left.restrict refines)
          (right.restrict refines) (bottom.restrict refines)
          (top.restrict refines)).bound := rfl
    _ <= (right.restrict refines).bound :=
      Clearance.Box.Boundary.Lines.boundaryOfLines_bound_le_right _ _ _ _
    _ = right.bound := VerticalLineClearance.restrict_bound _ _

/-- The transported boundary-clearance minimum is no larger than the retained bottom ambient-line bound. -/
private theorem ambientAfterMoveClearance_le_bottom
    {source target : Gaussian} (owner : Owner source)
    (leftSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientLeftClearance.bound)
    (rightSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientRightClearance.bound)
    (bottomSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientBottomClearance.bound)
    (topSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientTopClearance.bound) :
    (ambientAfterMoveClearance owner leftSmall rightSmall bottomSmall
      topSmall).bound <= (ambientBottomAfterMove owner bottomSmall).bound := by
  let left := ambientLeftAfterMove owner leftSmall
  let right := ambientRightAfterMove owner rightSmall
  let bottom := ambientBottomAfterMove owner bottomSmall
  let top := ambientTopAfterMove owner topSmall
  let refines := owner.track.initial.refinesAmbient
  calc
    (ambientAfterMoveClearance owner leftSmall rightSmall bottomSmall
        topSmall).bound =
        (Clearance.Box.Boundary.Lines.boundaryOfLines (left.restrict refines)
          (right.restrict refines) (bottom.restrict refines)
          (top.restrict refines)).bound := rfl
    _ <= (bottom.restrict refines).bound :=
      Clearance.Box.Boundary.Lines.boundaryOfLines_bound_le_bottom _ _ _ _
    _ = bottom.bound :=
      HorizontalLineClearance.restrict_bound _ _

/-- The transported boundary-clearance minimum is no larger than the retained top ambient-line bound. -/
private theorem ambientAfterMoveClearance_le_top
    {source target : Gaussian} (owner : Owner source)
    (leftSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientLeftClearance.bound)
    (rightSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientRightClearance.bound)
    (bottomSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientBottomClearance.bound)
    (topSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientTopClearance.bound) :
    (ambientAfterMoveClearance owner leftSmall rightSmall bottomSmall
      topSmall).bound <= (ambientTopAfterMove owner topSmall).bound := by
  let left := ambientLeftAfterMove owner leftSmall
  let right := ambientRightAfterMove owner rightSmall
  let bottom := ambientBottomAfterMove owner bottomSmall
  let top := ambientTopAfterMove owner topSmall
  let refines := owner.track.initial.refinesAmbient
  calc
    (ambientAfterMoveClearance owner leftSmall rightSmall bottomSmall
        topSmall).bound =
        (Clearance.Box.Boundary.Lines.boundaryOfLines (left.restrict refines)
          (right.restrict refines) (bottom.restrict refines)
          (top.restrict refines)).bound := rfl
    _ <= (top.restrict refines).bound :=
      Clearance.Box.Boundary.Lines.boundaryOfLines_bound_le_top _ _ _ _
    _ = top.bound :=
      HorizontalLineClearance.restrict_bound _ _

/-- Same-box Rouché transport with a requested target-clearance reserve.
The inexpensive transported-clearance branch is tried first; exact
resultants and finite Newton recentering remain a total fallback. -/
@[expose] def reservedTransport {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.clearance.bound) (reserve : Coordinate) :
    Owner target :=
  if same : source = target then
    same ▸ owner
  else
    let displacement :=
      Data.Gaussian.Norm.Basic.normSq (source - target)
    if leftSmall : displacement <
        owner.track.initial.ambientLeftClearance.bound then
      if rightSmall : displacement <
          owner.track.initial.ambientRightClearance.bound then
        if bottomSmall : displacement <
            owner.track.initial.ambientBottomClearance.bound then
          if topSmall : displacement <
              owner.track.initial.ambientTopClearance.bound then
            let carried := Riemann.RootContinuation.SquareRootContinuation.transportedOwner
              owner.track.initial small
            if _reserveSmall : reserve < carried.clearance.bound then
              ambientRoucheTransport owner targetNonzero small leftSmall
                rightSmall bottomSmall topSmall
            else
              resultantReservedTransport owner targetNonzero small reserve
          else resultantReservedTransport owner targetNonzero small reserve
        else resultantReservedTransport owner targetNonzero small reserve
      else resultantReservedTransport owner targetNonzero small reserve
    else resultantReservedTransport owner targetNonzero small reserve

/-- Equal source owners give equal reserved transports, independently of the
proof witnesses carried by the two calls. -/
theorem reservedTransport_congr_owner
    {source target : Gaussian} {left right : Owner source}
    (same : left = right)
    (leftTargetNonzero rightTargetNonzero : target ≠ 0)
    (leftSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      left.track.initial.clearance.bound)
    (rightSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      right.track.initial.clearance.bound)
    (reserve : Coordinate) :
    reservedTransport left leftTargetNonzero leftSmall reserve =
      reservedTransport right rightTargetNonzero rightSmall reserve := by
  subst right
  rfl

/-- Public structural cache for the inexpensive ambient-Rouché branch of
`reservedTransport`.  Downstream continuation proofs can use the retained box
and the fact that its boundary clearance controls every ambient line without
reopening the nested branch search. -/
structure AmbientReservedTransportCache {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.clearance.bound) (reserve : Coordinate)
    (leftSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientLeftClearance.bound)
    (rightSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientRightClearance.bound)
    (bottomSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientBottomClearance.bound)
    (topSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientTopClearance.bound) where
  /-- The selected original transport keeps the source initial box exactly. -/ initialBox :
    (reservedTransport owner targetNonzero small reserve).track.initial.box =
      owner.track.initial.box
  /-- The selected original transport keeps the source ambient exactly. -/ ambientBox :
    (reservedTransport owner targetNonzero small reserve).ambient = owner.ambient
  /-- The selected transport retains the exact computed left ambient-line bound. -/ ambientLeftBound :
    (reservedTransport owner targetNonzero small
        reserve).track.initial.ambientLeftClearance.bound =
      (ambientLeftAfterMove owner leftSmall).bound
  /-- The selected transport retains the exact computed right ambient-line bound. -/ ambientRightBound :
    (reservedTransport owner targetNonzero small
        reserve).track.initial.ambientRightClearance.bound =
      (ambientRightAfterMove owner rightSmall).bound
  /-- The selected transport retains the exact computed bottom ambient-line bound. -/ ambientBottomBound :
    (reservedTransport owner targetNonzero small
        reserve).track.initial.ambientBottomClearance.bound =
      (ambientBottomAfterMove owner bottomSmall).bound
  /-- The selected transport retains the exact computed top ambient-line bound. -/ ambientTopBound :
    (reservedTransport owner targetNonzero small
        reserve).track.initial.ambientTopClearance.bound =
      (ambientTopAfterMove owner topSmall).bound
  /-- The selected transport's boundary bound equals the minimum of its four actual transported line bounds. -/
    clearanceBound :
    (reservedTransport owner targetNonzero small
        reserve).track.initial.clearance.bound =
      min (ambientLeftAfterMove owner leftSmall).bound
        (min (ambientRightAfterMove owner rightSmall).bound
          (min (ambientBottomAfterMove owner bottomSmall).bound
            (ambientTopAfterMove owner topSmall).bound))
  /-- The selected transport's boundary minimum is no larger than its retained left ambient bound. -/
    clearanceLeAmbientLeft :
    (reservedTransport owner targetNonzero small
        reserve).track.initial.clearance.bound <=
      (reservedTransport owner targetNonzero small
        reserve).track.initial.ambientLeftClearance.bound
  /-- The selected transport's boundary minimum is no larger than its retained right ambient bound. -/
    clearanceLeAmbientRight :
    (reservedTransport owner targetNonzero small
        reserve).track.initial.clearance.bound <=
      (reservedTransport owner targetNonzero small
        reserve).track.initial.ambientRightClearance.bound
  /-- The selected transport's boundary minimum is no larger than its retained bottom ambient bound. -/
    clearanceLeAmbientBottom :
    (reservedTransport owner targetNonzero small
        reserve).track.initial.clearance.bound <=
      (reservedTransport owner targetNonzero small
        reserve).track.initial.ambientBottomClearance.bound
  /-- The selected transport's boundary minimum is no larger than its retained top ambient bound. -/
    clearanceLeAmbientTop :
    (reservedTransport owner targetNonzero small
        reserve).track.initial.clearance.bound <=
      (reservedTransport owner targetNonzero small
        reserve).track.initial.ambientTopClearance.bound

/-- Cache the selected ambient-Rouché transport branch from its exact rational
comparisons. -/
theorem reservedTransportAmbientCache {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.clearance.bound) (reserve : Coordinate)
    (different : source ≠ target)
    (leftSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientLeftClearance.bound)
    (rightSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientRightClearance.bound)
    (bottomSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientBottomClearance.bound)
    (topSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientTopClearance.bound)
    (reserveSmall : reserve <
      (Riemann.RootContinuation.SquareRootContinuation.transportedOwner
        owner.track.initial small).clearance.bound) :
    AmbientReservedTransportCache owner targetNonzero small reserve leftSmall
      rightSmall bottomSmall topSmall := by
  have selected : reservedTransport owner targetNonzero small reserve =
      ambientRoucheTransport owner targetNonzero small leftSmall rightSmall
        bottomSmall topSmall := by
    unfold reservedTransport
    rw [dif_neg different]
    dsimp only
    rw [dif_pos leftSmall, dif_pos rightSmall, dif_pos bottomSmall,
      dif_pos topSmall, dif_pos reserveSmall]
  refine
    { initialBox := by
        rw [selected]
        exact ambientRoucheTransport_initial_box owner targetNonzero small
          leftSmall rightSmall bottomSmall topSmall
      ambientBox := by
        rw [selected]
        exact ambientRoucheTransport_ambient owner targetNonzero small
          leftSmall rightSmall bottomSmall topSmall
      ambientLeftBound := by
        rw [selected]
        rfl
      ambientRightBound := by
        rw [selected]
        rfl
      ambientBottomBound := by
        rw [selected]
        rfl
      ambientTopBound := by
        rw [selected]
        rfl
      clearanceBound := by
        rw [selected]
        change (ambientAfterMoveClearance owner leftSmall rightSmall bottomSmall
          topSmall).bound = _
        exact ambientAfterMoveClearance_bound owner leftSmall rightSmall
          bottomSmall topSmall
      clearanceLeAmbientLeft := by
        rw [selected]
        change (ambientAfterMoveClearance owner leftSmall rightSmall bottomSmall
          topSmall).bound <= (ambientLeftAfterMove owner leftSmall).bound
        exact ambientAfterMoveClearance_le_left owner leftSmall rightSmall
          bottomSmall topSmall
      clearanceLeAmbientRight := by
        rw [selected]
        change (ambientAfterMoveClearance owner leftSmall rightSmall bottomSmall
          topSmall).bound <= (ambientRightAfterMove owner rightSmall).bound
        exact ambientAfterMoveClearance_le_right owner leftSmall rightSmall
          bottomSmall topSmall
      clearanceLeAmbientBottom := by
        rw [selected]
        change (ambientAfterMoveClearance owner leftSmall rightSmall bottomSmall
          topSmall).bound <= (ambientBottomAfterMove owner bottomSmall).bound
        exact ambientAfterMoveClearance_le_bottom owner leftSmall rightSmall
          bottomSmall topSmall
      clearanceLeAmbientTop := by
        rw [selected]
        change (ambientAfterMoveClearance owner leftSmall rightSmall bottomSmall
          topSmall).bound <= (ambientTopAfterMove owner topSmall).bound
        exact ambientAfterMoveClearance_le_top owner leftSmall rightSmall
          bottomSmall topSmall }

/-- The ambient branch cache packages the transported owner with the same
boundary-to-ambient dominance invariant. -/
theorem AmbientReservedTransportCache.ambientClearanceDominance
    {source target : Gaussian} {owner : Owner source}
    {targetNonzero : target ≠ 0}
    {small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.clearance.bound} {reserve : Coordinate}
    {leftSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientLeftClearance.bound}
    {rightSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientRightClearance.bound}
    {bottomSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientBottomClearance.bound}
    {topSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.ambientTopClearance.bound}
    (cache : AmbientReservedTransportCache owner targetNonzero small reserve
      leftSmall rightSmall bottomSmall topSmall) :
    AmbientClearanceDominance
      (reservedTransport owner targetNonzero small reserve) :=
  ⟨cache.clearanceLeAmbientLeft, cache.clearanceLeAmbientRight,
    cache.clearanceLeAmbientBottom, cache.clearanceLeAmbientTop⟩

/-- The finite collection of source-polynomial and box bounds needed to use
the uniform quadratic Horner estimate on all four ambient lines.  The data is
stable under the inexpensive same-box transport. -/
structure QuadraticAmbientBudget {parameter : Gaussian}
    (owner : Owner parameter) : Prop where
  /-- The original Gaussian parameter's squared norm is at most 256. -/ parameterNormSqLe :
    Data.Gaussian.Norm.Basic.normSq parameter ≤ 256
  /-- The original ambient vertical interval's square bound is at most 16. -/ verticalIntervalSqLe :
    (Box.Intervals.verticalInterval owner.ambient).squareBound ≤ 16
  /-- The original ambient horizontal interval's square bound is at most 16. -/ horizontalIntervalSqLe :
    (Box.Intervals.horizontalInterval owner.ambient).squareBound ≤ 16
  /-- The original initial box's left coordinate has square at most 16. -/ leftSqLe : owner.track.initial.box.xLower ^ 2
    ≤ 16
  /-- The original initial box's right coordinate has square at most 16. -/ rightSqLe : owner.track.initial.box.xUpper ^
    2 ≤ 16
  /-- The original initial box's bottom coordinate has square at most 16. -/ bottomSqLe : owner.track.initial.box.yLower
    ^ 2 ≤ 16
  /-- The original initial box's top coordinate has square at most 16. -/ topSqLe : owner.track.initial.box.yUpper ^ 2 ≤
    16

/-- Build the quadratic Horner budget from one explicitly cached owner box,
including boxes whose boundary meets a coordinate axis.

The exact original owner box and ambient identities retain its parameter norm, four coordinate squares and two interval
endpoint maxima in one budget. -/
theorem quadraticAmbientBudget_of_box_all {parameter : Gaussian}
    (owner : Owner parameter) (box : QuadraticBox)
    (initialBox : owner.track.initial.box = box)
    (ambientBox : owner.ambient = box)
    (parameterNormSqLe :
      Data.Gaussian.Norm.Basic.normSq parameter ≤ 256)
    (leftSqLe : box.xLower ^ 2 ≤ 16)
    (rightSqLe : box.xUpper ^ 2 ≤ 16)
    (bottomSqLe : box.yLower ^ 2 ≤ 16)
    (topSqLe : box.yUpper ^ 2 ≤ 16) :
    QuadraticAmbientBudget owner := by
  refine
    { parameterNormSqLe := parameterNormSqLe
      verticalIntervalSqLe := ?_
      horizontalIntervalSqLe := ?_
      leftSqLe := ?_
      rightSqLe := ?_
      bottomSqLe := ?_
      topSqLe := ?_ }
  · rw [ambientBox]
    exact Basic.max_le bottomSqLe topSqLe
  · rw [ambientBox]
    exact Basic.max_le leftSqLe rightSqLe
  · rw [initialBox]
    exact leftSqLe
  · rw [initialBox]
    exact rightSqLe
  · rw [initialBox]
    exact bottomSqLe
  · rw [initialBox]
    exact topSqLe

/-- Compatibility wrapper for callers that already cache nonzero box
coordinates.  The general finite Horner estimate no longer needs them. -/
theorem quadraticAmbientBudget_of_box {parameter : Gaussian}
    (owner : Owner parameter) (box : QuadraticBox)
    (initialBox : owner.track.initial.box = box)
    (ambientBox : owner.ambient = box)
    (parameterNormSqLe :
      Data.Gaussian.Norm.Basic.normSq parameter ≤ 256)
    (_leftNonzero : box.xLower ≠ 0) (_rightNonzero : box.xUpper ≠ 0)
    (_bottomNonzero : box.yLower ≠ 0) (_topNonzero : box.yUpper ≠ 0)
    (leftSqLe : box.xLower ^ 2 ≤ 16)
    (rightSqLe : box.xUpper ^ 2 ≤ 16)
    (bottomSqLe : box.yLower ^ 2 ≤ 16)
    (topSqLe : box.yUpper ^ 2 ≤ 16) :
    QuadraticAmbientBudget owner :=
  quadraticAmbientBudget_of_box_all owner box initialBox ambientBox
    parameterNormSqLe leftSqLe rightSqLe bottomSqLe topSqLe

/-- One fixed positive clearance floor shared by the explicit quadratic
examples.  Its displayed factors record the `1/2` Rouché margin and the
`65536` four-side Horner budget. -/
@[expose] def quadraticAmbientTransportFloor : Fraction.Rational :=
  ((1 : Coordinate) / 2) ^ 2 / (4 * 65536)

/-- Transport floor obtained from an explicitly cached residual margin.  The
fixed `quadraticAmbientTransportFloor` is the special case `margin = 1 / 2`;
worked paths may use smaller positive margins without discarding the same
finite Horner calculation. -/
@[expose] def quadraticAmbientTransportFloorAt (margin : Coordinate) : Fraction.Rational :=
  margin ^ 2 / (4 * 65536)

/-- The fixed transport floor is the parametric floor evaluated at the half-unit margin. -/
theorem quadraticAmbientTransportFloor_eq_at_half :
    quadraticAmbientTransportFloor =
      quadraticAmbientTransportFloorAt ((1 : Coordinate) / 2) := rfl

/-- A positive residual margin gives a positive parametric quadratic transport floor. -/
theorem quadraticAmbientTransportFloorAt_pos (margin : Coordinate)
    (positive : 0 < margin) :
    0 < quadraticAmbientTransportFloorAt margin := by
  unfold quadraticAmbientTransportFloorAt
  exact Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Arithmetic.pow_pos_direct positive 2)
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 65536) (by decide)))

/-- The fixed half-unit quadratic transport floor is positive. -/
theorem quadraticAmbientTransportFloor_pos :
    0 < quadraticAmbientTransportFloor := by
  unfold quadraticAmbientTransportFloor
  exact Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Arithmetic.pow_pos_direct
      (Fraction.Order.Field.div_pos_direct (by decide) (by decide)) 2)
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 65536) (by decide)))

/-- The fixed half-unit floor bounds a side transport with at least that margin and majorant between 1 and 65536. -/
private theorem quadraticAmbientTransportFloor_le_side
    (margin majorant : Coordinate)
    (marginLower : (1 : Coordinate) / 2 ≤ margin)
    (majorantOne : 1 ≤ majorant) (majorantLe : majorant ≤ 65536) :
    quadraticAmbientTransportFloor ≤ margin ^ 2 / (4 * majorant) := by
  have halfPositive : (0 : Coordinate) < 1 / 2 :=
    Fraction.Order.Field.div_pos_direct (by decide) (by decide)
  have marginNonnegative : 0 ≤ margin := halfPositive.le.trans marginLower
  have numeratorLe : ((1 : Coordinate) / 2) ^ 2 ≤ margin ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct halfPositive.le marginLower 2
  have majorantPositive : (0 : Coordinate) < majorant :=
    (show (0 : Coordinate) < 1 by decide).trans_le majorantOne
  have denominatorPositive : (0 : Coordinate) < 4 * majorant :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide) majorantPositive
  have denominatorLe : 4 * majorant ≤ (4 : Coordinate) * 65536 :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct majorantLe
      (by decide)
  calc
    quadraticAmbientTransportFloor =
        ((1 : Coordinate) / 2) ^ 2 / (4 * 65536) := rfl
    _ ≤ ((1 : Coordinate) / 2) ^ 2 / (4 * majorant) :=
      Fraction.Order.Field.div_le_div_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.sq_nonneg_direct ((1 : Coordinate) / 2))
        denominatorPositive denominatorLe
    _ ≤ margin ^ 2 / (4 * majorant) := by
      change ((1 : Coordinate) / 2) ^ 2 * (4 * majorant)⁻¹ ≤
        margin ^ 2 * (4 * majorant)⁻¹
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        numeratorLe
        (Fraction.Order.Field.inv_pos_direct denominatorPositive).le

/-- A nonnegative retained margin floor bounds the side transport when its majorant lies between 1 and 65536. -/
private theorem quadraticAmbientTransportFloorAt_le_side
    (floor margin majorant : Coordinate)
    (floorNonnegative : 0 ≤ floor) (floorLe : floor ≤ margin)
    (majorantOne : 1 ≤ majorant) (majorantLe : majorant ≤ 65536) :
    quadraticAmbientTransportFloorAt floor ≤
      margin ^ 2 / (4 * majorant) := by
  have marginNonnegative : 0 ≤ margin := floorNonnegative.trans floorLe
  have numeratorLe : floor ^ 2 ≤ margin ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct floorNonnegative floorLe 2
  have majorantPositive : (0 : Coordinate) < majorant :=
    (show (0 : Coordinate) < 1 by decide).trans_le majorantOne
  have denominatorPositive : (0 : Coordinate) < 4 * majorant :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide) majorantPositive
  have denominatorLe : 4 * majorant ≤ (4 : Coordinate) * 65536 :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct majorantLe
      (by decide)
  calc
    quadraticAmbientTransportFloorAt floor =
        floor ^ 2 / (4 * 65536) := rfl
    _ ≤ floor ^ 2 / (4 * majorant) :=
      Fraction.Order.Field.div_le_div_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.sq_nonneg_direct floor)
        denominatorPositive denominatorLe
    _ ≤ margin ^ 2 / (4 * majorant) := by
      change floor ^ 2 * (4 * majorant)⁻¹ ≤
        margin ^ 2 * (4 * majorant)⁻¹
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        numeratorLe
        (Fraction.Order.Field.inv_pos_direct denominatorPositive).le

/-- A generated residual and exact cached side majorant can retain an
independently chosen transport floor.  The final rational `tradeoff` is the
only relation between those two cached quantities, so certificate generators
need not round either one to a small fixed menu of powers of two. -/
theorem retainedQuadraticAmbientTransportFloor_le_side
    (retainedFloor residualFloor margin majorant sideUpper : Coordinate)
    (residualFloorPositive : 0 < residualFloor)
    (residualFloorLe : residualFloor ≤ margin)
    (majorantOne : 1 ≤ majorant) (majorantLe : majorant ≤ sideUpper)
    (tradeoff : quadraticAmbientTransportFloorAt retainedFloor ≤
      residualFloor ^ 2 / (4 * sideUpper)) :
    quadraticAmbientTransportFloorAt retainedFloor ≤
      margin ^ 2 / (4 * majorant) := by
  have numeratorLe : residualFloor ^ 2 ≤ margin ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct residualFloorPositive.le
      residualFloorLe 2
  have majorantPositive : (0 : Coordinate) < majorant :=
    (show (0 : Coordinate) < 1 by decide).trans_le majorantOne
  have denominatorPositive : (0 : Coordinate) < 4 * majorant :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide) majorantPositive
  have denominatorLe : 4 * majorant ≤ 4 * sideUpper :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct majorantLe
      (by decide)
  calc
    quadraticAmbientTransportFloorAt retainedFloor ≤
        residualFloor ^ 2 / (4 * sideUpper) := tradeoff
    _ ≤ residualFloor ^ 2 / (4 * majorant) :=
      Fraction.Order.Field.div_le_div_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.sq_nonneg_direct residualFloor)
        denominatorPositive denominatorLe
    _ ≤ margin ^ 2 / (4 * majorant) := by
      change residualFloor ^ 2 * (4 * majorant)⁻¹ ≤
        margin ^ 2 * (4 * majorant)⁻¹
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        numeratorLe
        (Fraction.Order.Field.inv_pos_direct denominatorPositive).le

/-- The sharp `16384` side budget trades fourfold denominator slack for a
twofold smaller residual margin while preserving the existing eighth-unit
transport floor. -/
private theorem eighthTransportFloor_le_side_of_sixteenthMargin
    (margin majorant : Coordinate)
    (marginLower : (1 : Coordinate) / 16 ≤ margin)
    (majorantOne : 1 ≤ majorant) (majorantLe : majorant ≤ 16384) :
    quadraticAmbientTransportFloorAt (1 / 8 : Coordinate) ≤
      margin ^ 2 / (4 * majorant) := by
  have sixteenthPositive : (0 : Coordinate) < 1 / 16 :=
    Fraction.Order.Field.div_pos_direct (by decide) (by decide)
  have marginNonnegative : 0 ≤ margin :=
    sixteenthPositive.le.trans marginLower
  have numeratorLe : ((1 : Coordinate) / 16) ^ 2 ≤ margin ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct sixteenthPositive.le
      marginLower 2
  have majorantPositive : (0 : Coordinate) < majorant :=
    (show (0 : Coordinate) < 1 by decide).trans_le majorantOne
  have denominatorPositive : (0 : Coordinate) < 4 * majorant :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide) majorantPositive
  have denominatorLe : 4 * majorant ≤ (4 : Coordinate) * 16384 :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct majorantLe
      (by decide)
  calc
    quadraticAmbientTransportFloorAt (1 / 8 : Coordinate) =
        ((1 : Coordinate) / 16) ^ 2 / (4 * 16384) := by
      unfold quadraticAmbientTransportFloorAt
      have oneEighth : (1 / 8 : Coordinate) = 2 * (1 / 16) := by
        decide
      apply Fraction.Field.div_eq_div_of_cross_mul
        (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 65536) (by decide))).ne'
        (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 16384) (by decide))).ne'
      rw [oneEighth]
      ring1
    _ ≤ ((1 : Coordinate) / 16) ^ 2 / (4 * majorant) :=
      Fraction.Order.Field.div_le_div_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.sq_nonneg_direct
          ((1 : Coordinate) / 16)) denominatorPositive denominatorLe
    _ ≤ margin ^ 2 / (4 * majorant) := by
      change ((1 : Coordinate) / 16) ^ 2 * (4 * majorant)⁻¹ ≤
        margin ^ 2 * (4 * majorant)⁻¹
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        numeratorLe
        (Fraction.Order.Field.inv_pos_direct denominatorPositive).le

/-- An exact side majorant below `256` lets an eighth-unit transport floor
survive from only a one-hundred-twenty-eighth-unit residual margin.

The retained margin and side majorant bounds control the numerator and positive denominator of the same rational
transport floor. Multiplication by the original inverse preserves the comparison. -/
private theorem eighthTransportFloor_le_side_of_oneTwentyEighthMargin
    (margin majorant : Coordinate)
    (marginLower : (1 : Coordinate) / 128 ≤ margin)
    (majorantOne : 1 ≤ majorant) (majorantLe : majorant ≤ 256) :
    quadraticAmbientTransportFloorAt (1 / 8 : Coordinate) ≤
      margin ^ 2 / (4 * majorant) := by
  have floorPositive : (0 : Coordinate) < 1 / 128 :=
    Fraction.Order.Field.div_pos_direct
      (Fraction.Cast.Order.natCast_pos_direct (n := 1) (by omega))
      (Fraction.Cast.Order.natCast_pos_direct (n := 128) (by omega))
  have numeratorLe : ((1 : Coordinate) / 128) ^ 2 ≤ margin ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct floorPositive.le
      marginLower 2
  have majorantPositive : (0 : Coordinate) < majorant :=
    (show (0 : Coordinate) < 1 by decide).trans_le majorantOne
  have denominatorPositive : (0 : Coordinate) < 4 * majorant :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide) majorantPositive
  have denominatorLe : 4 * majorant ≤ (4 : Coordinate) * 256 :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct majorantLe
      (by decide)
  calc
    quadraticAmbientTransportFloorAt (1 / 8 : Coordinate) =
        ((1 : Coordinate) / 128) ^ 2 / (4 * 256) := by
      unfold quadraticAmbientTransportFloorAt
      have oneEighth : (1 / 8 : Coordinate) = 16 * (1 / 128) := by
        calc
          (1 / 8 : Coordinate) = 16 / 128 := by
            apply Fraction.Field.div_eq_div_of_cross_mul
              (Fraction.Cast.Order.natCast_pos_direct
                (n := 8) (by omega)).ne'
              (Fraction.Cast.Order.natCast_pos_direct
                (n := 128) (by omega)).ne'
            ring1
          _ = 16 * (1 / 128) := by
            rw [Fraction.Field.div_eq_mul_inv_direct,
              Fraction.Field.div_eq_mul_inv_direct,
              Fraction.Field.one_mul]
      apply Fraction.Field.div_eq_div_of_cross_mul
        (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 65536) (by decide))).ne'
        (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 256) (by decide))).ne'
      rw [oneEighth]
      ring1
    _ ≤ ((1 : Coordinate) / 128) ^ 2 / (4 * majorant) :=
      Fraction.Order.Field.div_le_div_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.sq_nonneg_direct
          ((1 : Coordinate) / 128)) denominatorPositive denominatorLe
    _ ≤ margin ^ 2 / (4 * majorant) := by
      change _ * (4 * majorant)⁻¹ ≤ _ * (4 * majorant)⁻¹
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct numeratorLe
        (Fraction.Order.Field.inv_pos_direct denominatorPositive).le

/-- A three-two-hundred-fifty-sixths residual supports the same eighth-unit
transport floor for exact side majorants bounded by `512`.

The retained margin and side majorant bounds control the numerator and positive denominator of the same rational
transport floor. Multiplication by the original inverse preserves the comparison. -/
private theorem eighthTransportFloor_le_side_of_threeTwoFiftySixthMargin
    (margin majorant : Coordinate)
    (marginLower : (3 : Coordinate) / 256 ≤ margin)
    (majorantOne : 1 ≤ majorant) (majorantLe : majorant ≤ 512) :
    quadraticAmbientTransportFloorAt (1 / 8 : Coordinate) ≤
      margin ^ 2 / (4 * majorant) := by
  have residualPositive : (0 : Coordinate) < 3 / 256 :=
    Fraction.Order.Field.div_pos_direct
      (Fraction.Cast.Order.natCast_pos_direct (n := 3) (by omega))
      (Fraction.Cast.Order.natCast_pos_direct (n := 256) (by omega))
  have numeratorLe : ((3 : Coordinate) / 256) ^ 2 ≤ margin ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct residualPositive.le
      marginLower 2
  have majorantPositive : (0 : Coordinate) < majorant :=
    (show (0 : Coordinate) < 1 by decide).trans_le majorantOne
  have denominatorPositive : (0 : Coordinate) < 4 * majorant :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide) majorantPositive
  have denominatorLe : 4 * majorant ≤ (4 : Coordinate) * 512 :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct majorantLe
      (by decide)
  have baseline :
      quadraticAmbientTransportFloorAt (1 / 8 : Coordinate) ≤
        ((3 : Coordinate) / 256) ^ 2 / (4 * 512) := by
    have floorEq :
        quadraticAmbientTransportFloorAt (1 / 8 : Coordinate) =
          (1 / 16777216 : Coordinate) := by
      unfold quadraticAmbientTransportFloorAt
      have square : (1 / 8 : Coordinate) ^ 2 = 1 / 64 := by
        rw [pow_two, Fraction.Field.div_mul_div_direct]
        apply Fraction.Field.div_eq_div_of_cross_mul
          (Fraction.Field.mul_ne_zero_direct
            (Fraction.Cast.Order.natCast_pos_direct
              (n := 8) (by omega)).ne'
            (Fraction.Cast.Order.natCast_pos_direct
              (n := 8) (by omega)).ne')
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 64) (by omega)).ne'
        ring1
      rw [square]
      apply Fraction.Field.div_eq_div_of_cross_mul
        (Fraction.Field.mul_ne_zero_direct
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 4) (by omega)).ne'
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 65536) (by omega)).ne')
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 16777216) (by omega)).ne'
      have cancelSixtyFour : (1 / 64 : Coordinate) * 64 = 1 :=
        Fraction.Field.div_mul_cancel_of_ne _ _
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 64) (by omega)).ne'
      calc
        (1 / 64 : Coordinate) * 16777216 =
            ((1 / 64 : Coordinate) * 64) * 262144 := by ring1
        _ = 262144 := by rw [cancelSixtyFour]; ring1
        _ = (1 : Coordinate) * (4 * 65536) := by ring1
    have baselineEq : ((3 : Coordinate) / 256) ^ 2 / (4 * 512) =
        9 / 134217728 := by
      have square : ((3 : Coordinate) / 256) ^ 2 = 9 / 65536 := by
        rw [pow_two, Fraction.Field.div_mul_div_direct]
        apply Fraction.Field.div_eq_div_of_cross_mul
          (Fraction.Field.mul_ne_zero_direct
            (Fraction.Cast.Order.natCast_pos_direct
              (n := 256) (by omega)).ne'
            (Fraction.Cast.Order.natCast_pos_direct
              (n := 256) (by omega)).ne')
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 65536) (by omega)).ne'
        ring1
      rw [square]
      apply Fraction.Field.div_eq_div_of_cross_mul
        (Fraction.Field.mul_ne_zero_direct
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 4) (by omega)).ne'
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 512) (by omega)).ne')
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 134217728) (by omega)).ne'
      have cancelSixtyFiveThousand :
          (9 / 65536 : Coordinate) * 65536 = 9 :=
        Fraction.Field.div_mul_cancel_of_ne _ _
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 65536) (by omega)).ne'
      calc
        (9 / 65536 : Coordinate) * 134217728 =
            ((9 / 65536 : Coordinate) * 65536) * 2048 := by ring1
        _ = 18432 := by rw [cancelSixtyFiveThousand]; ring1
        _ = (9 : Coordinate) * (4 * 512) := by ring1
    rw [floorEq, baselineEq,
      show (1 / 16777216 : Coordinate) = 8 / 134217728 by
        apply Fraction.Field.div_eq_div_of_cross_mul
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 16777216) (by omega)).ne'
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 134217728) (by omega)).ne'
        ring1]
    simp only [Fraction.Field.div_eq_mul_inv_direct]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Cast.Order.natCast_le_direct
        (m := 8) (n := 9) (by omega))
      (Fraction.Order.Field.inv_pos_direct
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 134217728) (by omega))).le
  calc
    quadraticAmbientTransportFloorAt (1 / 8 : Coordinate) ≤
        ((3 : Coordinate) / 256) ^ 2 / (4 * 512) := baseline
    _ ≤ ((3 : Coordinate) / 256) ^ 2 / (4 * majorant) :=
      Fraction.Order.Field.div_le_div_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.sq_nonneg_direct
          ((3 : Coordinate) / 256)) denominatorPositive denominatorLe
    _ ≤ margin ^ 2 / (4 * majorant) := by
      change _ * (4 * majorant)⁻¹ ≤ _ * (4 * majorant)⁻¹
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct numeratorLe
        (Fraction.Order.Field.inv_pos_direct denominatorPositive).le

/-- An exact side majorant below `1024` lets an eighth-unit transport floor
survive from a one-sixty-fourth-unit residual margin.

The retained margin and side majorant bounds control the numerator and positive denominator of the same rational
transport floor. Multiplication by the original inverse preserves the comparison. -/
private theorem eighthTransportFloor_le_side_of_sixtyFourthMargin
    (margin majorant : Coordinate)
    (marginLower : (1 : Coordinate) / 64 ≤ margin)
    (majorantOne : 1 ≤ majorant) (majorantLe : majorant ≤ 1024) :
    quadraticAmbientTransportFloorAt (1 / 8 : Coordinate) ≤
      margin ^ 2 / (4 * majorant) := by
  have floorPositive : (0 : Coordinate) < 1 / 64 :=
    Fraction.Order.Field.div_pos_direct
      (Fraction.Cast.Order.natCast_pos_direct (n := 1) (by omega))
      (Fraction.Cast.Order.natCast_pos_direct (n := 64) (by omega))
  have numeratorLe : ((1 : Coordinate) / 64) ^ 2 ≤ margin ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct floorPositive.le
      marginLower 2
  have majorantPositive : (0 : Coordinate) < majorant :=
    (show (0 : Coordinate) < 1 by decide).trans_le majorantOne
  have denominatorPositive : (0 : Coordinate) < 4 * majorant :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide) majorantPositive
  have denominatorLe : 4 * majorant ≤ (4 : Coordinate) * 1024 :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct majorantLe
      (by decide)
  calc
    quadraticAmbientTransportFloorAt (1 / 8 : Coordinate) =
        ((1 : Coordinate) / 64) ^ 2 / (4 * 1024) := by
      unfold quadraticAmbientTransportFloorAt
      have oneEighth : (1 / 8 : Coordinate) = 8 * (1 / 64) := by
        calc
          (1 / 8 : Coordinate) = 8 / 64 := by
            apply Fraction.Field.div_eq_div_of_cross_mul
              (Fraction.Cast.Order.natCast_pos_direct
                (n := 8) (by omega)).ne'
              (Fraction.Cast.Order.natCast_pos_direct
                (n := 64) (by omega)).ne'
            ring1
          _ = 8 * (1 / 64) := by
            rw [Fraction.Field.div_eq_mul_inv_direct,
              Fraction.Field.div_eq_mul_inv_direct,
              Fraction.Field.one_mul]
      apply Fraction.Field.div_eq_div_of_cross_mul
        (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 65536) (by decide))).ne'
        (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 1024) (by decide))).ne'
      rw [oneEighth]
      ring1
    _ ≤ ((1 : Coordinate) / 64) ^ 2 / (4 * majorant) :=
      Fraction.Order.Field.div_le_div_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.sq_nonneg_direct
          ((1 : Coordinate) / 64)) denominatorPositive denominatorLe
    _ ≤ margin ^ 2 / (4 * majorant) := by
      change _ * (4 * majorant)⁻¹ ≤ _ * (4 * majorant)⁻¹
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct numeratorLe
        (Fraction.Order.Field.inv_pos_direct denominatorPositive).le

/-- Exact quadratic side-majorant data cached on the current owner geometry. -/
structure QuadraticAmbientSideMajorantBounds {parameter : Gaussian}
    (owner : Owner parameter) (bound : Coordinate) : Prop where
  /-- The actual quadratic left side majorant on the original owner's ambient interval is at most the supplied bound. -/
    left : Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        Riemann.RootContinuation.SquareRootDegree.degreeTwo)
      (Gaussian.Cast.Winding.verticalBase owner.track.initial.box.xLower)
      Gaussian.Constants.imaginaryUnit
      (Box.Intervals.verticalInterval owner.ambient) ≤ bound
  /-- The actual quadratic right side majorant on the original owner's ambient interval is at most the supplied bound.
  -/ right : Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        Riemann.RootContinuation.SquareRootDegree.degreeTwo)
      (Gaussian.Cast.Winding.verticalBase owner.track.initial.box.xUpper)
      Gaussian.Constants.imaginaryUnit
      (Box.Intervals.verticalInterval owner.ambient) ≤ bound
  /-- The actual quadratic bottom side majorant on the original owner's ambient interval is at most the supplied bound.
  -/ bottom : Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        Riemann.RootContinuation.SquareRootDegree.degreeTwo)
      (Gaussian.Cast.Imaginary.horizontalBase owner.track.initial.box.yLower)
      Gaussian.Constants.horizontalDirection
      (Box.Intervals.horizontalInterval owner.ambient) ≤ bound
  /-- The actual quadratic top side majorant on the original owner's ambient interval is at most the supplied bound. -/
    top : Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        Riemann.RootContinuation.SquareRootDegree.degreeTwo)
      (Gaussian.Cast.Imaginary.horizontalBase owner.track.initial.box.yUpper)
      Gaussian.Constants.horizontalDirection
      (Box.Intervals.horizontalInterval owner.ambient) ≤ bound

/-- The same four exact side bounds cached on an explicit rational box. -/
structure QuadraticBoxSideMajorantBounds (parameter : Gaussian)
    (box : QuadraticBox) (bound : Coordinate) : Prop where
  /-- The actual quadratic left side majorant on the exact retained box interval is at most the supplied bound. -/ left
    : Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        Riemann.RootContinuation.SquareRootDegree.degreeTwo)
      (Gaussian.Cast.Winding.verticalBase box.xLower)
      Gaussian.Constants.imaginaryUnit
      (Box.Intervals.verticalInterval box) ≤ bound
  /-- The actual quadratic right side majorant on the exact retained box interval is at most the supplied bound. -/
    right : Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        Riemann.RootContinuation.SquareRootDegree.degreeTwo)
      (Gaussian.Cast.Winding.verticalBase box.xUpper)
      Gaussian.Constants.imaginaryUnit
      (Box.Intervals.verticalInterval box) ≤ bound
  /-- The actual quadratic bottom side majorant on the exact retained box interval is at most the supplied bound. -/
    bottom : Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        Riemann.RootContinuation.SquareRootDegree.degreeTwo)
      (Gaussian.Cast.Imaginary.horizontalBase box.yLower)
      Gaussian.Constants.horizontalDirection
      (Box.Intervals.horizontalInterval box) ≤ bound
  /-- The actual quadratic top side majorant on the exact retained box interval is at most the supplied bound. -/ top :
    Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
        Riemann.RootContinuation.SquareRootDegree.degreeTwo)
      (Gaussian.Cast.Imaginary.horizontalBase box.yUpper)
      Gaussian.Constants.horizontalDirection
      (Box.Intervals.horizontalInterval box) ≤ bound

/-- A smaller finite parameter interval cannot increase the executable side
majorant.

The same two finite real and imaginary Horner bounds decrease with the supplied interval refinement; their original
summed rational floor at one preserves that comparison. -/
theorem boundarySideMajorant_le_of_intervalRefines
    (polynomial : GaussianPolynomial) (base direction : Gaussian)
    {interval root : Data.Rat.Interval.Bounds}
    (refines : interval.Refines root) :
    Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant polynomial base direction
        interval ≤
      Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant polynomial base direction
        root := by
  unfold Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
  apply Basic.max_le (Basic.le_max_left _ _)
  exact (Fraction.Order.Arithmetic.add_le_add_direct
    (Dense.Rational.Bounds.Horner.evalSqBound_le_of_refines _ refines)
    (Dense.Rational.Bounds.Horner.evalSqBound_le_of_refines _ refines)).trans
      (Basic.le_max_right _ _)

/-- Restrict an explicit box-side cache to an owner whose box agrees and
whose ambient is a subbox. -/
theorem quadraticAmbientSideMajorantBounds_of_box
    {parameter : Gaussian} (owner : Owner parameter) (box : QuadraticBox)
    (bound : Coordinate) (boxEq : owner.track.initial.box = box)
    (ambientRefines : owner.ambient.Refines box)
    (bounds : QuadraticBoxSideMajorantBounds parameter box bound) :
    QuadraticAmbientSideMajorantBounds owner bound := by
  have verticalRefines : Refines
      (Box.Intervals.verticalInterval owner.ambient)
      (Box.Intervals.verticalInterval box) :=
    ⟨ambientRefines.2.2.1, ambientRefines.2.2.2⟩
  have horizontalRefines : Refines
      (Box.Intervals.horizontalInterval owner.ambient)
      (Box.Intervals.horizontalInterval box) :=
    ⟨ambientRefines.1, ambientRefines.2.1⟩
  constructor
  · rw [boxEq]
    exact (boundarySideMajorant_le_of_intervalRefines _ _ _
      verticalRefines).trans bounds.left
  · rw [boxEq]
    exact (boundarySideMajorant_le_of_intervalRefines _ _ _
      verticalRefines).trans bounds.right
  · rw [boxEq]
    exact (boundarySideMajorant_le_of_intervalRefines _ _ _
      horizontalRefines).trans bounds.bottom
  · rw [boxEq]
    exact (boundarySideMajorant_le_of_intervalRefines _ _ _
      horizontalRefines).trans bounds.top
/-- Structural and quantitative result of ambient transport at an arbitrary
positive cached residual margin. -/
structure ParametricQuadraticAmbientTransportCache {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.clearance.bound)
    (marginFloor : Coordinate) where
  /-- The actual zero-reserve transport retains the original source box. -/ initialBox :
    (reservedTransport owner targetNonzero small 0).track.initial.box =
      owner.track.initial.box
  /-- The actual zero-reserve transport retains the original ambient box. -/ ambientBox :
    (reservedTransport owner targetNonzero small 0).ambient = owner.ambient
  /-- The supplied positive residual-margin floor bounds the actual transported boundary clearance from below. -/
    clearanceFloor : quadraticAmbientTransportFloorAt marginFloor ≤
    (reservedTransport owner targetNonzero small 0).track.initial.clearance.bound
  /-- The actual transported left ambient bound is at most one quarter of the original left bound squared. -/
    ambientLeftQuarterSq :
    (reservedTransport owner targetNonzero small
        0).track.initial.ambientLeftClearance.bound ≤
      owner.track.initial.ambientLeftClearance.bound ^ 2 / 4
  /-- The actual transported boundary bound is at most one quarter of the original left ambient bound squared. -/
    clearanceQuarterSq :
    (reservedTransport owner targetNonzero small
        0).track.initial.clearance.bound ≤
      owner.track.initial.ambientLeftClearance.bound ^ 2 / 4
  /-- The retained transported owner's boundary bound controls every ambient-line bound. -/ dominance :
    AmbientClearanceDominance
    (reservedTransport owner targetNonzero small 0)
  /-- The retained transported owner satisfies the original finite quadratic parameter and box budget. -/ budget :
    QuadraticAmbientBudget
    (reservedTransport owner targetNonzero small 0)

/-- A positive exact residual margin and the cached radius/parameter budgets
construct a successor cache without imposing the older half-unit floor.

The exact source owner, target parameter and supplied quantitative bounds retain the original ambient refinement, four
side clearances and selected transport floor in this cache. -/
theorem parametricQuadraticAmbientTransportCache {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.clearance.bound)
    (different : source ≠ target)
    (dominance : AmbientClearanceDominance owner)
    (marginFloor : Coordinate) (marginFloorPositive : 0 < marginFloor)
    (marginLower : marginFloor ≤
      owner.track.initial.clearance.bound -
        Data.Gaussian.Norm.Basic.normSq (source - target))
    (budget : QuadraticAmbientBudget owner)
    (targetNormSqLe :
      Data.Gaussian.Norm.Basic.normSq target ≤ 256) :
    ParametricQuadraticAmbientTransportCache owner targetNonzero small
      marginFloor := by
  let displacement :=
    Data.Gaussian.Norm.Basic.normSq (source - target)
  have ambientSmall := dominance.ambientSmallness small
  have leftSmall := ambientSmall.1
  have rightSmall := ambientSmall.2.1
  have bottomSmall := ambientSmall.2.2.1
  have topSmall := ambientSmall.2.2.2
  have reserveSmall : (0 : Coordinate) <
      (Riemann.RootContinuation.SquareRootContinuation.transportedOwner
        owner.track.initial small).clearance.bound :=
    (Riemann.RootContinuation.SquareRootContinuation.transportedOwner
      owner.track.initial small).clearance.positive
  let ambientCache := reservedTransportAmbientCache owner targetNonzero small 0
    different leftSmall rightSmall bottomSmall topSmall reserveSmall
  have leftMargin : marginFloor ≤
      owner.track.initial.ambientLeftClearance.bound - displacement :=
    marginLower.trans
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct dominance.left
        displacement)
  have rightMargin : marginFloor ≤
      owner.track.initial.ambientRightClearance.bound - displacement :=
    marginLower.trans
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct dominance.right
        displacement)
  have bottomMargin : marginFloor ≤
      owner.track.initial.ambientBottomClearance.bound - displacement :=
    marginLower.trans
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct dominance.bottom
        displacement)
  have topMargin : marginFloor ≤
      owner.track.initial.ambientTopClearance.bound - displacement :=
    marginLower.trans
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct dominance.top
        displacement)
  have leftMajorantLe :
      Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial source
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Winding.verticalBase owner.track.initial.box.xLower)
        Gaussian.Constants.imaginaryUnit
        (Box.Intervals.verticalInterval owner.ambient) ≤ 65536 :=
    quadraticVerticalBoundarySideMajorant_le source
      owner.track.initial.box.xLower
      (Box.Intervals.verticalInterval owner.ambient)
      budget.verticalIntervalSqLe budget.leftSqLe budget.parameterNormSqLe
  have rightMajorantLe :
      Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial source
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Winding.verticalBase owner.track.initial.box.xUpper)
        Gaussian.Constants.imaginaryUnit
        (Box.Intervals.verticalInterval owner.ambient) ≤ 65536 :=
    quadraticVerticalBoundarySideMajorant_le source
      owner.track.initial.box.xUpper
      (Box.Intervals.verticalInterval owner.ambient)
      budget.verticalIntervalSqLe budget.rightSqLe budget.parameterNormSqLe
  have bottomMajorantLe :
      Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial source
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Imaginary.horizontalBase owner.track.initial.box.yLower)
        Gaussian.Constants.horizontalDirection
        (Box.Intervals.horizontalInterval owner.ambient) ≤ 65536 :=
    quadraticHorizontalBoundarySideMajorant_le source
      owner.track.initial.box.yLower
      (Box.Intervals.horizontalInterval owner.ambient)
      budget.horizontalIntervalSqLe budget.bottomSqLe budget.parameterNormSqLe
  have topMajorantLe :
      Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial source
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Imaginary.horizontalBase owner.track.initial.box.yUpper)
        Gaussian.Constants.horizontalDirection
        (Box.Intervals.horizontalInterval owner.ambient) ≤ 65536 :=
    quadraticHorizontalBoundarySideMajorant_le source
      owner.track.initial.box.yUpper
      (Box.Intervals.horizontalInterval owner.ambient)
      budget.horizontalIntervalSqLe budget.topSqLe budget.parameterNormSqLe
  have leftFloor : quadraticAmbientTransportFloorAt marginFloor ≤
      (ambientLeftAfterMove owner leftSmall).bound := by
    rw [ambientLeftAfterMove,
      Power.Clearance.Box.Transport.verticalClearanceAfterMove_bound]
    exact quadraticAmbientTransportFloorAt_le_side _ _ _
      marginFloorPositive.le leftMargin (Basic.le_max_left _ _) leftMajorantLe
  have rightFloor : quadraticAmbientTransportFloorAt marginFloor ≤
      (ambientRightAfterMove owner rightSmall).bound := by
    rw [ambientRightAfterMove,
      Power.Clearance.Box.Transport.verticalClearanceAfterMove_bound]
    exact quadraticAmbientTransportFloorAt_le_side _ _ _
      marginFloorPositive.le rightMargin (Basic.le_max_left _ _) rightMajorantLe
  have bottomFloor : quadraticAmbientTransportFloorAt marginFloor ≤
      (ambientBottomAfterMove owner bottomSmall).bound := by
    rw [ambientBottomAfterMove,
      Power.Clearance.Box.Transport.horizontalClearanceAfterMove_bound]
    exact quadraticAmbientTransportFloorAt_le_side _ _ _
      marginFloorPositive.le bottomMargin (Basic.le_max_left _ _) bottomMajorantLe
  have topFloor : quadraticAmbientTransportFloorAt marginFloor ≤
      (ambientTopAfterMove owner topSmall).bound := by
    rw [ambientTopAfterMove,
      Power.Clearance.Box.Transport.horizontalClearanceAfterMove_bound]
    exact quadraticAmbientTransportFloorAt_le_side _ _ _
      marginFloorPositive.le topMargin (Basic.le_max_left _ _) topMajorantLe
  refine
    { initialBox := ambientCache.initialBox
      ambientBox := ambientCache.ambientBox
      clearanceFloor := ?_
      ambientLeftQuarterSq := ?_
      clearanceQuarterSq := ?_
      dominance := ambientCache.ambientClearanceDominance
      budget := ?_ }
  · rw [ambientCache.clearanceBound]
    exact le_min leftFloor (le_min rightFloor (le_min bottomFloor topFloor))
  · rw [ambientCache.ambientLeftBound]
    exact ambientLeftAfterMove_bound_le_quarter_sq owner leftSmall
  · exact ambientCache.clearanceLeAmbientLeft.trans
      (ambientCache.ambientLeftBound.le.trans
        (ambientLeftAfterMove_bound_le_quarter_sq owner leftSmall))
  · refine
      { parameterNormSqLe := targetNormSqLe
        verticalIntervalSqLe := ?_
        horizontalIntervalSqLe := ?_
        leftSqLe := ?_
        rightSqLe := ?_
        bottomSqLe := ?_
        topSqLe := ?_ }
    · rw [ambientCache.ambientBox]
      exact budget.verticalIntervalSqLe
    · rw [ambientCache.ambientBox]
      exact budget.horizontalIntervalSqLe
    · rw [ambientCache.initialBox]
      exact budget.leftSqLe
    · rw [ambientCache.initialBox]
      exact budget.rightSqLe
    · rw [ambientCache.initialBox]
      exact budget.bottomSqLe
    · rw [ambientCache.initialBox]
      exact budget.topSqLe

/-- Exact-majorant specialization of ambient transport.  A generated
certificate supplies its residual floor, side-majorant cap, and the one
rational tradeoff proving that they retain the requested successor floor.

The exact source owner, target parameter and supplied quantitative bounds retain the original ambient refinement, four
side clearances and selected transport floor in this cache. -/
theorem retainedFloorQuadraticAmbientTransportCache
    {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.clearance.bound)
    (different : source ≠ target)
    (dominance : AmbientClearanceDominance owner)
    (retainedFloor residualFloor sideUpper : Coordinate)
    (residualFloorPositive : 0 < residualFloor)
    (marginLower : residualFloor ≤
      owner.track.initial.clearance.bound -
        Data.Gaussian.Norm.Basic.normSq (source - target))
    (sideBounds : QuadraticAmbientSideMajorantBounds owner sideUpper)
    (tradeoff : quadraticAmbientTransportFloorAt retainedFloor ≤
      residualFloor ^ 2 / (4 * sideUpper))
    (budget : QuadraticAmbientBudget owner)
    (targetNormSqLe :
      Data.Gaussian.Norm.Basic.normSq target ≤ 256) :
    ParametricQuadraticAmbientTransportCache owner targetNonzero small
      retainedFloor := by
  let displacement :=
    Data.Gaussian.Norm.Basic.normSq (source - target)
  have ambientSmall := dominance.ambientSmallness small
  have leftSmall := ambientSmall.1
  have rightSmall := ambientSmall.2.1
  have bottomSmall := ambientSmall.2.2.1
  have topSmall := ambientSmall.2.2.2
  have reserveSmall : (0 : Coordinate) <
      (Riemann.RootContinuation.SquareRootContinuation.transportedOwner
        owner.track.initial small).clearance.bound :=
    (Riemann.RootContinuation.SquareRootContinuation.transportedOwner
      owner.track.initial small).clearance.positive
  let ambientCache := reservedTransportAmbientCache owner targetNonzero small 0
    different leftSmall rightSmall bottomSmall topSmall reserveSmall
  have leftMargin : residualFloor ≤
      owner.track.initial.ambientLeftClearance.bound - displacement :=
    marginLower.trans
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct dominance.left
        displacement)
  have rightMargin : residualFloor ≤
      owner.track.initial.ambientRightClearance.bound - displacement :=
    marginLower.trans
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct dominance.right
        displacement)
  have bottomMargin : residualFloor ≤
      owner.track.initial.ambientBottomClearance.bound - displacement :=
    marginLower.trans
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct dominance.bottom
        displacement)
  have topMargin : residualFloor ≤
      owner.track.initial.ambientTopClearance.bound - displacement :=
    marginLower.trans
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct dominance.top
        displacement)
  have leftFloor : quadraticAmbientTransportFloorAt retainedFloor ≤
      (ambientLeftAfterMove owner leftSmall).bound := by
    rw [ambientLeftAfterMove,
      Power.Clearance.Box.Transport.verticalClearanceAfterMove_bound]
    exact retainedQuadraticAmbientTransportFloor_le_side retainedFloor
      residualFloor _ _ sideUpper residualFloorPositive leftMargin
        (Basic.le_max_left _ _) sideBounds.left tradeoff
  have rightFloor : quadraticAmbientTransportFloorAt retainedFloor ≤
      (ambientRightAfterMove owner rightSmall).bound := by
    rw [ambientRightAfterMove,
      Power.Clearance.Box.Transport.verticalClearanceAfterMove_bound]
    exact retainedQuadraticAmbientTransportFloor_le_side retainedFloor
      residualFloor _ _ sideUpper residualFloorPositive rightMargin
        (Basic.le_max_left _ _) sideBounds.right tradeoff
  have bottomFloor : quadraticAmbientTransportFloorAt retainedFloor ≤
      (ambientBottomAfterMove owner bottomSmall).bound := by
    rw [ambientBottomAfterMove,
      Power.Clearance.Box.Transport.horizontalClearanceAfterMove_bound]
    exact retainedQuadraticAmbientTransportFloor_le_side retainedFloor
      residualFloor _ _ sideUpper residualFloorPositive bottomMargin
        (Basic.le_max_left _ _) sideBounds.bottom tradeoff
  have topFloor : quadraticAmbientTransportFloorAt retainedFloor ≤
      (ambientTopAfterMove owner topSmall).bound := by
    rw [ambientTopAfterMove,
      Power.Clearance.Box.Transport.horizontalClearanceAfterMove_bound]
    exact retainedQuadraticAmbientTransportFloor_le_side retainedFloor
      residualFloor _ _ sideUpper residualFloorPositive topMargin
        (Basic.le_max_left _ _) sideBounds.top tradeoff
  refine
    { initialBox := ambientCache.initialBox
      ambientBox := ambientCache.ambientBox
      clearanceFloor := ?_
      ambientLeftQuarterSq := ?_
      clearanceQuarterSq := ?_
      dominance := ambientCache.ambientClearanceDominance
      budget := ?_ }
  · rw [ambientCache.clearanceBound]
    exact le_min leftFloor (le_min rightFloor (le_min bottomFloor topFloor))
  · rw [ambientCache.ambientLeftBound]
    exact ambientLeftAfterMove_bound_le_quarter_sq owner leftSmall
  · exact ambientCache.clearanceLeAmbientLeft.trans
      (ambientCache.ambientLeftBound.le.trans
        (ambientLeftAfterMove_bound_le_quarter_sq owner leftSmall))
  · refine
      { parameterNormSqLe := targetNormSqLe
        verticalIntervalSqLe := ?_
        horizontalIntervalSqLe := ?_
        leftSqLe := ?_
        rightSqLe := ?_
        bottomSqLe := ?_
        topSqLe := ?_ }
    · rw [ambientCache.ambientBox]
      exact budget.verticalIntervalSqLe
    · rw [ambientCache.ambientBox]
      exact budget.horizontalIntervalSqLe
    · rw [ambientCache.initialBox]
      exact budget.leftSqLe
    · rw [ambientCache.initialBox]
      exact budget.rightSqLe
    · rw [ambientCache.initialBox]
      exact budget.bottomSqLe
    · rw [ambientCache.initialBox]
      exact budget.topSqLe

/-- A sixteenth-unit residual margin retains the older eighth-unit clearance
floor when the exact quadratic side calculation uses its sharp `16384`
budget.  This is the cached transport used by closely spaced explicit cells.

The supplied original margin, parameter and side-majorant bounds retain all four transported side certificates and their
same positive eighth-floor comparison. -/
theorem eighthFloorQuadraticAmbientTransportCache_of_sixteenthMargin
    {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.clearance.bound)
    (different : source ≠ target)
    (dominance : AmbientClearanceDominance owner)
    (marginLower : (1 : Coordinate) / 16 ≤
      owner.track.initial.clearance.bound -
        Data.Gaussian.Norm.Basic.normSq (source - target))
    (budget : QuadraticAmbientBudget owner)
    (targetNormSqLe :
      Data.Gaussian.Norm.Basic.normSq target ≤ 256) :
    ParametricQuadraticAmbientTransportCache owner targetNonzero small
      (1 / 8 : Coordinate) := by
  let displacement :=
    Data.Gaussian.Norm.Basic.normSq (source - target)
  have ambientSmall := dominance.ambientSmallness small
  have leftSmall := ambientSmall.1
  have rightSmall := ambientSmall.2.1
  have bottomSmall := ambientSmall.2.2.1
  have topSmall := ambientSmall.2.2.2
  have reserveSmall : (0 : Coordinate) <
      (Riemann.RootContinuation.SquareRootContinuation.transportedOwner
        owner.track.initial small).clearance.bound :=
    (Riemann.RootContinuation.SquareRootContinuation.transportedOwner
      owner.track.initial small).clearance.positive
  let ambientCache := reservedTransportAmbientCache owner targetNonzero small 0
    different leftSmall rightSmall bottomSmall topSmall reserveSmall
  have leftMargin : (1 : Coordinate) / 16 ≤
      owner.track.initial.ambientLeftClearance.bound - displacement :=
    marginLower.trans
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct dominance.left
        displacement)
  have rightMargin : (1 : Coordinate) / 16 ≤
      owner.track.initial.ambientRightClearance.bound - displacement :=
    marginLower.trans
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct dominance.right
        displacement)
  have bottomMargin : (1 : Coordinate) / 16 ≤
      owner.track.initial.ambientBottomClearance.bound - displacement :=
    marginLower.trans
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct dominance.bottom
        displacement)
  have topMargin : (1 : Coordinate) / 16 ≤
      owner.track.initial.ambientTopClearance.bound - displacement :=
    marginLower.trans
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct dominance.top
        displacement)
  have leftMajorantLe :
      Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial source
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Winding.verticalBase owner.track.initial.box.xLower)
        Gaussian.Constants.imaginaryUnit
        (Box.Intervals.verticalInterval owner.ambient) ≤ 16384 :=
    quadraticVerticalBoundarySideMajorant_le_16384 source
      owner.track.initial.box.xLower
      (Box.Intervals.verticalInterval owner.ambient)
      budget.verticalIntervalSqLe budget.leftSqLe budget.parameterNormSqLe
  have rightMajorantLe :
      Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial source
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Winding.verticalBase owner.track.initial.box.xUpper)
        Gaussian.Constants.imaginaryUnit
        (Box.Intervals.verticalInterval owner.ambient) ≤ 16384 :=
    quadraticVerticalBoundarySideMajorant_le_16384 source
      owner.track.initial.box.xUpper
      (Box.Intervals.verticalInterval owner.ambient)
      budget.verticalIntervalSqLe budget.rightSqLe budget.parameterNormSqLe
  have bottomMajorantLe :
      Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial source
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Imaginary.horizontalBase owner.track.initial.box.yLower)
        Gaussian.Constants.horizontalDirection
        (Box.Intervals.horizontalInterval owner.ambient) ≤ 16384 :=
    quadraticHorizontalBoundarySideMajorant_le_16384 source
      owner.track.initial.box.yLower
      (Box.Intervals.horizontalInterval owner.ambient)
      budget.horizontalIntervalSqLe budget.bottomSqLe budget.parameterNormSqLe
  have topMajorantLe :
      Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial source
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Imaginary.horizontalBase owner.track.initial.box.yUpper)
        Gaussian.Constants.horizontalDirection
        (Box.Intervals.horizontalInterval owner.ambient) ≤ 16384 :=
    quadraticHorizontalBoundarySideMajorant_le_16384 source
      owner.track.initial.box.yUpper
      (Box.Intervals.horizontalInterval owner.ambient)
      budget.horizontalIntervalSqLe budget.topSqLe budget.parameterNormSqLe
  have leftFloor : quadraticAmbientTransportFloorAt (1 / 8 : Coordinate) ≤
      (ambientLeftAfterMove owner leftSmall).bound := by
    rw [ambientLeftAfterMove,
      Power.Clearance.Box.Transport.verticalClearanceAfterMove_bound]
    exact eighthTransportFloor_le_side_of_sixteenthMargin _ _ leftMargin
      (Basic.le_max_left _ _) leftMajorantLe
  have rightFloor : quadraticAmbientTransportFloorAt (1 / 8 : Coordinate) ≤
      (ambientRightAfterMove owner rightSmall).bound := by
    rw [ambientRightAfterMove,
      Power.Clearance.Box.Transport.verticalClearanceAfterMove_bound]
    exact eighthTransportFloor_le_side_of_sixteenthMargin _ _ rightMargin
      (Basic.le_max_left _ _) rightMajorantLe
  have bottomFloor : quadraticAmbientTransportFloorAt (1 / 8 : Coordinate) ≤
      (ambientBottomAfterMove owner bottomSmall).bound := by
    rw [ambientBottomAfterMove,
      Power.Clearance.Box.Transport.horizontalClearanceAfterMove_bound]
    exact eighthTransportFloor_le_side_of_sixteenthMargin _ _ bottomMargin
      (Basic.le_max_left _ _) bottomMajorantLe
  have topFloor : quadraticAmbientTransportFloorAt (1 / 8 : Coordinate) ≤
      (ambientTopAfterMove owner topSmall).bound := by
    rw [ambientTopAfterMove,
      Power.Clearance.Box.Transport.horizontalClearanceAfterMove_bound]
    exact eighthTransportFloor_le_side_of_sixteenthMargin _ _ topMargin
      (Basic.le_max_left _ _) topMajorantLe
  refine
    { initialBox := ambientCache.initialBox
      ambientBox := ambientCache.ambientBox
      clearanceFloor := ?_
      ambientLeftQuarterSq := ?_
      clearanceQuarterSq := ?_
      dominance := ambientCache.ambientClearanceDominance
      budget := ?_ }
  · rw [ambientCache.clearanceBound]
    exact le_min leftFloor (le_min rightFloor (le_min bottomFloor topFloor))
  · rw [ambientCache.ambientLeftBound]
    exact ambientLeftAfterMove_bound_le_quarter_sq owner leftSmall
  · exact ambientCache.clearanceLeAmbientLeft.trans
      (ambientCache.ambientLeftBound.le.trans
        (ambientLeftAfterMove_bound_le_quarter_sq owner leftSmall))
  · refine
      { parameterNormSqLe := targetNormSqLe
        verticalIntervalSqLe := ?_
        horizontalIntervalSqLe := ?_
        leftSqLe := ?_
        rightSqLe := ?_
        bottomSqLe := ?_
        topSqLe := ?_ }
    · rw [ambientCache.ambientBox]
      exact budget.verticalIntervalSqLe
    · rw [ambientCache.ambientBox]
      exact budget.horizontalIntervalSqLe
    · rw [ambientCache.initialBox]
      exact budget.leftSqLe
    · rw [ambientCache.initialBox]
      exact budget.rightSqLe
    · rw [ambientCache.initialBox]
      exact budget.bottomSqLe
    · rw [ambientCache.initialBox]
      exact budget.topSqLe

/-- A cached exact `256` side budget preserves the established eighth-unit
clearance floor from a one-hundred-twenty-eighth-unit residual margin.

The supplied original margin, parameter and side-majorant bounds retain all four transported side certificates and their
same positive eighth-floor comparison. -/
theorem eighthFloorQuadraticAmbientTransportCache_of_oneTwentyEighthMargin
    {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.clearance.bound)
    (different : source ≠ target)
    (dominance : AmbientClearanceDominance owner)
    (marginLower : (1 : Coordinate) / 128 ≤
      owner.track.initial.clearance.bound -
        Data.Gaussian.Norm.Basic.normSq (source - target))
    (sideBounds : QuadraticAmbientSideMajorantBounds owner 256)
    (budget : QuadraticAmbientBudget owner)
    (targetNormSqLe :
      Data.Gaussian.Norm.Basic.normSq target ≤ 256) :
    ParametricQuadraticAmbientTransportCache owner targetNonzero small
      (1 / 8 : Coordinate) := by
  let displacement :=
    Data.Gaussian.Norm.Basic.normSq (source - target)
  have ambientSmall := dominance.ambientSmallness small
  have leftSmall := ambientSmall.1
  have rightSmall := ambientSmall.2.1
  have bottomSmall := ambientSmall.2.2.1
  have topSmall := ambientSmall.2.2.2
  have reserveSmall : (0 : Coordinate) <
      (Riemann.RootContinuation.SquareRootContinuation.transportedOwner
        owner.track.initial small).clearance.bound :=
    (Riemann.RootContinuation.SquareRootContinuation.transportedOwner
      owner.track.initial small).clearance.positive
  let ambientCache := reservedTransportAmbientCache owner targetNonzero small 0
    different leftSmall rightSmall bottomSmall topSmall reserveSmall
  have leftMargin : (1 : Coordinate) / 128 ≤
      owner.track.initial.ambientLeftClearance.bound - displacement :=
    marginLower.trans
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct dominance.left
        displacement)
  have rightMargin : (1 : Coordinate) / 128 ≤
      owner.track.initial.ambientRightClearance.bound - displacement :=
    marginLower.trans
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct dominance.right
        displacement)
  have bottomMargin : (1 : Coordinate) / 128 ≤
      owner.track.initial.ambientBottomClearance.bound - displacement :=
    marginLower.trans
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct dominance.bottom
        displacement)
  have topMargin : (1 : Coordinate) / 128 ≤
      owner.track.initial.ambientTopClearance.bound - displacement :=
    marginLower.trans
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct dominance.top
        displacement)
  have leftFloor : quadraticAmbientTransportFloorAt (1 / 8 : Coordinate) ≤
      (ambientLeftAfterMove owner leftSmall).bound := by
    rw [ambientLeftAfterMove,
      Power.Clearance.Box.Transport.verticalClearanceAfterMove_bound]
    exact eighthTransportFloor_le_side_of_oneTwentyEighthMargin _ _ leftMargin
      (Basic.le_max_left _ _) sideBounds.left
  have rightFloor : quadraticAmbientTransportFloorAt (1 / 8 : Coordinate) ≤
      (ambientRightAfterMove owner rightSmall).bound := by
    rw [ambientRightAfterMove,
      Power.Clearance.Box.Transport.verticalClearanceAfterMove_bound]
    exact eighthTransportFloor_le_side_of_oneTwentyEighthMargin _ _ rightMargin
      (Basic.le_max_left _ _) sideBounds.right
  have bottomFloor : quadraticAmbientTransportFloorAt (1 / 8 : Coordinate) ≤
      (ambientBottomAfterMove owner bottomSmall).bound := by
    rw [ambientBottomAfterMove,
      Power.Clearance.Box.Transport.horizontalClearanceAfterMove_bound]
    exact eighthTransportFloor_le_side_of_oneTwentyEighthMargin _ _ bottomMargin
      (Basic.le_max_left _ _) sideBounds.bottom
  have topFloor : quadraticAmbientTransportFloorAt (1 / 8 : Coordinate) ≤
      (ambientTopAfterMove owner topSmall).bound := by
    rw [ambientTopAfterMove,
      Power.Clearance.Box.Transport.horizontalClearanceAfterMove_bound]
    exact eighthTransportFloor_le_side_of_oneTwentyEighthMargin _ _ topMargin
      (Basic.le_max_left _ _) sideBounds.top
  refine
    { initialBox := ambientCache.initialBox
      ambientBox := ambientCache.ambientBox
      clearanceFloor := ?_
      ambientLeftQuarterSq := ?_
      clearanceQuarterSq := ?_
      dominance := ambientCache.ambientClearanceDominance
      budget := ?_ }
  · rw [ambientCache.clearanceBound]
    exact le_min leftFloor (le_min rightFloor (le_min bottomFloor topFloor))
  · rw [ambientCache.ambientLeftBound]
    exact ambientLeftAfterMove_bound_le_quarter_sq owner leftSmall
  · exact ambientCache.clearanceLeAmbientLeft.trans
      (ambientCache.ambientLeftBound.le.trans
        (ambientLeftAfterMove_bound_le_quarter_sq owner leftSmall))
  · refine
      { parameterNormSqLe := targetNormSqLe
        verticalIntervalSqLe := ?_
        horizontalIntervalSqLe := ?_
        leftSqLe := ?_
        rightSqLe := ?_
        bottomSqLe := ?_
        topSqLe := ?_ }
    · rw [ambientCache.ambientBox]
      exact budget.verticalIntervalSqLe
    · rw [ambientCache.ambientBox]
      exact budget.horizontalIntervalSqLe
    · rw [ambientCache.initialBox]
      exact budget.leftSqLe
    · rw [ambientCache.initialBox]
      exact budget.rightSqLe
    · rw [ambientCache.initialBox]
      exact budget.bottomSqLe
    · rw [ambientCache.initialBox]
      exact budget.topSqLe

/-- A cached `512` side budget preserves the established eighth-unit
clearance floor from a three-two-hundred-fifty-sixths-unit residual margin.

The supplied original margin, parameter and side-majorant bounds retain all four transported side certificates and their
same positive eighth-floor comparison. -/
theorem eighthFloorQuadraticAmbientTransportCache_of_threeTwoFiftySixthMargin
    {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.clearance.bound)
    (different : source ≠ target)
    (dominance : AmbientClearanceDominance owner)
    (marginLower : (3 : Coordinate) / 256 ≤
      owner.track.initial.clearance.bound -
        Data.Gaussian.Norm.Basic.normSq (source - target))
    (sideBounds : QuadraticAmbientSideMajorantBounds owner 512)
    (budget : QuadraticAmbientBudget owner)
    (targetNormSqLe :
      Data.Gaussian.Norm.Basic.normSq target ≤ 256) :
    ParametricQuadraticAmbientTransportCache owner targetNonzero small
      (1 / 8 : Coordinate) := by
  let displacement :=
    Data.Gaussian.Norm.Basic.normSq (source - target)
  have ambientSmall := dominance.ambientSmallness small
  have leftSmall := ambientSmall.1
  have rightSmall := ambientSmall.2.1
  have bottomSmall := ambientSmall.2.2.1
  have topSmall := ambientSmall.2.2.2
  have reserveSmall : (0 : Coordinate) <
      (Riemann.RootContinuation.SquareRootContinuation.transportedOwner
        owner.track.initial small).clearance.bound :=
    (Riemann.RootContinuation.SquareRootContinuation.transportedOwner
      owner.track.initial small).clearance.positive
  let ambientCache := reservedTransportAmbientCache owner targetNonzero small 0
    different leftSmall rightSmall bottomSmall topSmall reserveSmall
  have leftMargin : (3 : Coordinate) / 256 ≤
      owner.track.initial.ambientLeftClearance.bound - displacement :=
    marginLower.trans
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct dominance.left
        displacement)
  have rightMargin : (3 : Coordinate) / 256 ≤
      owner.track.initial.ambientRightClearance.bound - displacement :=
    marginLower.trans
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct dominance.right
        displacement)
  have bottomMargin : (3 : Coordinate) / 256 ≤
      owner.track.initial.ambientBottomClearance.bound - displacement :=
    marginLower.trans
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct dominance.bottom
        displacement)
  have topMargin : (3 : Coordinate) / 256 ≤
      owner.track.initial.ambientTopClearance.bound - displacement :=
    marginLower.trans
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct dominance.top
        displacement)
  have leftFloor : quadraticAmbientTransportFloorAt (1 / 8 : Coordinate) ≤
      (ambientLeftAfterMove owner leftSmall).bound := by
    rw [ambientLeftAfterMove,
      Power.Clearance.Box.Transport.verticalClearanceAfterMove_bound]
    exact eighthTransportFloor_le_side_of_threeTwoFiftySixthMargin _ _ leftMargin
      (Basic.le_max_left _ _) sideBounds.left
  have rightFloor : quadraticAmbientTransportFloorAt (1 / 8 : Coordinate) ≤
      (ambientRightAfterMove owner rightSmall).bound := by
    rw [ambientRightAfterMove,
      Power.Clearance.Box.Transport.verticalClearanceAfterMove_bound]
    exact eighthTransportFloor_le_side_of_threeTwoFiftySixthMargin _ _ rightMargin
      (Basic.le_max_left _ _) sideBounds.right
  have bottomFloor : quadraticAmbientTransportFloorAt (1 / 8 : Coordinate) ≤
      (ambientBottomAfterMove owner bottomSmall).bound := by
    rw [ambientBottomAfterMove,
      Power.Clearance.Box.Transport.horizontalClearanceAfterMove_bound]
    exact eighthTransportFloor_le_side_of_threeTwoFiftySixthMargin _ _ bottomMargin
      (Basic.le_max_left _ _) sideBounds.bottom
  have topFloor : quadraticAmbientTransportFloorAt (1 / 8 : Coordinate) ≤
      (ambientTopAfterMove owner topSmall).bound := by
    rw [ambientTopAfterMove,
      Power.Clearance.Box.Transport.horizontalClearanceAfterMove_bound]
    exact eighthTransportFloor_le_side_of_threeTwoFiftySixthMargin _ _ topMargin
      (Basic.le_max_left _ _) sideBounds.top
  refine
    { initialBox := ambientCache.initialBox
      ambientBox := ambientCache.ambientBox
      clearanceFloor := ?_
      ambientLeftQuarterSq := ?_
      clearanceQuarterSq := ?_
      dominance := ambientCache.ambientClearanceDominance
      budget := ?_ }
  · rw [ambientCache.clearanceBound]
    exact le_min leftFloor (le_min rightFloor (le_min bottomFloor topFloor))
  · rw [ambientCache.ambientLeftBound]
    exact ambientLeftAfterMove_bound_le_quarter_sq owner leftSmall
  · exact ambientCache.clearanceLeAmbientLeft.trans
      (ambientCache.ambientLeftBound.le.trans
        (ambientLeftAfterMove_bound_le_quarter_sq owner leftSmall))
  · refine
      { parameterNormSqLe := targetNormSqLe
        verticalIntervalSqLe := ?_
        horizontalIntervalSqLe := ?_
        leftSqLe := ?_
        rightSqLe := ?_
        bottomSqLe := ?_
        topSqLe := ?_ }
    · rw [ambientCache.ambientBox]
      exact budget.verticalIntervalSqLe
    · rw [ambientCache.ambientBox]
      exact budget.horizontalIntervalSqLe
    · rw [ambientCache.initialBox]
      exact budget.leftSqLe
    · rw [ambientCache.initialBox]
      exact budget.rightSqLe
    · rw [ambientCache.initialBox]
      exact budget.bottomSqLe
    · rw [ambientCache.initialBox]
      exact budget.topSqLe

/-- A cached `1024` side budget preserves the established eighth-unit
clearance floor from a one-sixty-fourth-unit residual margin.

The supplied original margin, parameter and side-majorant bounds retain all four transported side certificates and their
same positive eighth-floor comparison. -/
theorem eighthFloorQuadraticAmbientTransportCache_of_sixtyFourthMargin
    {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.clearance.bound)
    (different : source ≠ target)
    (dominance : AmbientClearanceDominance owner)
    (marginLower : (1 : Coordinate) / 64 ≤
      owner.track.initial.clearance.bound -
        Data.Gaussian.Norm.Basic.normSq (source - target))
    (sideBounds : QuadraticAmbientSideMajorantBounds owner 1024)
    (budget : QuadraticAmbientBudget owner)
    (targetNormSqLe :
      Data.Gaussian.Norm.Basic.normSq target ≤ 256) :
    ParametricQuadraticAmbientTransportCache owner targetNonzero small
      (1 / 8 : Coordinate) := by
  let displacement :=
    Data.Gaussian.Norm.Basic.normSq (source - target)
  have ambientSmall := dominance.ambientSmallness small
  have leftSmall := ambientSmall.1
  have rightSmall := ambientSmall.2.1
  have bottomSmall := ambientSmall.2.2.1
  have topSmall := ambientSmall.2.2.2
  have reserveSmall : (0 : Coordinate) <
      (Riemann.RootContinuation.SquareRootContinuation.transportedOwner
        owner.track.initial small).clearance.bound :=
    (Riemann.RootContinuation.SquareRootContinuation.transportedOwner
      owner.track.initial small).clearance.positive
  let ambientCache := reservedTransportAmbientCache owner targetNonzero small 0
    different leftSmall rightSmall bottomSmall topSmall reserveSmall
  have leftMargin : (1 : Coordinate) / 64 ≤
      owner.track.initial.ambientLeftClearance.bound - displacement :=
    marginLower.trans
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct dominance.left
        displacement)
  have rightMargin : (1 : Coordinate) / 64 ≤
      owner.track.initial.ambientRightClearance.bound - displacement :=
    marginLower.trans
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct dominance.right
        displacement)
  have bottomMargin : (1 : Coordinate) / 64 ≤
      owner.track.initial.ambientBottomClearance.bound - displacement :=
    marginLower.trans
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct dominance.bottom
        displacement)
  have topMargin : (1 : Coordinate) / 64 ≤
      owner.track.initial.ambientTopClearance.bound - displacement :=
    marginLower.trans
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct dominance.top
        displacement)
  have leftFloor : quadraticAmbientTransportFloorAt (1 / 8 : Coordinate) ≤
      (ambientLeftAfterMove owner leftSmall).bound := by
    rw [ambientLeftAfterMove,
      Power.Clearance.Box.Transport.verticalClearanceAfterMove_bound]
    exact eighthTransportFloor_le_side_of_sixtyFourthMargin _ _ leftMargin
      (Basic.le_max_left _ _) sideBounds.left
  have rightFloor : quadraticAmbientTransportFloorAt (1 / 8 : Coordinate) ≤
      (ambientRightAfterMove owner rightSmall).bound := by
    rw [ambientRightAfterMove,
      Power.Clearance.Box.Transport.verticalClearanceAfterMove_bound]
    exact eighthTransportFloor_le_side_of_sixtyFourthMargin _ _ rightMargin
      (Basic.le_max_left _ _) sideBounds.right
  have bottomFloor : quadraticAmbientTransportFloorAt (1 / 8 : Coordinate) ≤
      (ambientBottomAfterMove owner bottomSmall).bound := by
    rw [ambientBottomAfterMove,
      Power.Clearance.Box.Transport.horizontalClearanceAfterMove_bound]
    exact eighthTransportFloor_le_side_of_sixtyFourthMargin _ _ bottomMargin
      (Basic.le_max_left _ _) sideBounds.bottom
  have topFloor : quadraticAmbientTransportFloorAt (1 / 8 : Coordinate) ≤
      (ambientTopAfterMove owner topSmall).bound := by
    rw [ambientTopAfterMove,
      Power.Clearance.Box.Transport.horizontalClearanceAfterMove_bound]
    exact eighthTransportFloor_le_side_of_sixtyFourthMargin _ _ topMargin
      (Basic.le_max_left _ _) sideBounds.top
  refine
    { initialBox := ambientCache.initialBox
      ambientBox := ambientCache.ambientBox
      clearanceFloor := ?_
      ambientLeftQuarterSq := ?_
      clearanceQuarterSq := ?_
      dominance := ambientCache.ambientClearanceDominance
      budget := ?_ }
  · rw [ambientCache.clearanceBound]
    exact le_min leftFloor (le_min rightFloor (le_min bottomFloor topFloor))
  · rw [ambientCache.ambientLeftBound]
    exact ambientLeftAfterMove_bound_le_quarter_sq owner leftSmall
  · exact ambientCache.clearanceLeAmbientLeft.trans
      (ambientCache.ambientLeftBound.le.trans
        (ambientLeftAfterMove_bound_le_quarter_sq owner leftSmall))
  · refine
      { parameterNormSqLe := targetNormSqLe
        verticalIntervalSqLe := ?_
        horizontalIntervalSqLe := ?_
        leftSqLe := ?_
        rightSqLe := ?_
        bottomSqLe := ?_
        topSqLe := ?_ }
    · rw [ambientCache.ambientBox]
      exact budget.verticalIntervalSqLe
    · rw [ambientCache.ambientBox]
      exact budget.horizontalIntervalSqLe
    · rw [ambientCache.initialBox]
      exact budget.leftSqLe
    · rw [ambientCache.initialBox]
      exact budget.rightSqLe
    · rw [ambientCache.initialBox]
      exact budget.bottomSqLe
    · rw [ambientCache.initialBox]
      exact budget.topSqLe

/-- Structural and quantitative result of one uniform inexpensive quadratic
transport.  This cache is deliberately independent of the proof witnesses
used by the nested executable branch selection. -/
structure QuadraticAmbientTransportCache {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.clearance.bound) where
  /-- The actual zero-reserve transport retains the original source box. -/ initialBox :
    (reservedTransport owner targetNonzero small 0).track.initial.box =
      owner.track.initial.box
  /-- The actual zero-reserve transport retains the original ambient box. -/ ambientBox :
    (reservedTransport owner targetNonzero small 0).ambient = owner.ambient
  /-- The fixed half-unit floor bounds the actual transported boundary clearance from below. -/ clearanceFloor :
    quadraticAmbientTransportFloor ≤
    (reservedTransport owner targetNonzero small 0).track.initial.clearance.bound
  /-- The actual transported left ambient bound is at most one quarter of the original left bound squared. -/
    ambientLeftQuarterSq :
    (reservedTransport owner targetNonzero small
        0).track.initial.ambientLeftClearance.bound ≤
      owner.track.initial.ambientLeftClearance.bound ^ 2 / 4
  /-- The actual transported boundary bound is at most one quarter of the original left ambient bound squared. -/
    clearanceQuarterSq :
    (reservedTransport owner targetNonzero small
        0).track.initial.clearance.bound ≤
      owner.track.initial.ambientLeftClearance.bound ^ 2 / 4
  /-- The retained transported owner's boundary bound controls every ambient-line bound. -/ dominance :
    AmbientClearanceDominance
    (reservedTransport owner targetNonzero small 0)
  /-- The retained transported owner satisfies the original finite quadratic parameter and box budget. -/ budget :
    QuadraticAmbientBudget
    (reservedTransport owner targetNonzero small 0)

/-- A half-unit residual margin and the cached radius-`4`/parameter-`16`
budgets construct the complete successor cache in one step.

The exact source owner, target parameter and supplied quantitative bounds retain the original ambient refinement, four
side clearances and selected transport floor in this cache. -/
theorem quadraticAmbientTransportCache {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.clearance.bound)
    (different : source ≠ target)
    (dominance : AmbientClearanceDominance owner)
    (marginLower : (1 : Coordinate) / 2 ≤
      owner.track.initial.clearance.bound -
        Data.Gaussian.Norm.Basic.normSq (source - target))
    (budget : QuadraticAmbientBudget owner)
    (targetNormSqLe :
      Data.Gaussian.Norm.Basic.normSq target ≤ 256) :
    QuadraticAmbientTransportCache owner targetNonzero small := by
  let displacement :=
    Data.Gaussian.Norm.Basic.normSq (source - target)
  have ambientSmall := dominance.ambientSmallness small
  have leftSmall := ambientSmall.1
  have rightSmall := ambientSmall.2.1
  have bottomSmall := ambientSmall.2.2.1
  have topSmall := ambientSmall.2.2.2
  have reserveSmall : (0 : Coordinate) <
      (Riemann.RootContinuation.SquareRootContinuation.transportedOwner
        owner.track.initial small).clearance.bound :=
    (Riemann.RootContinuation.SquareRootContinuation.transportedOwner
      owner.track.initial small).clearance.positive
  let ambientCache := reservedTransportAmbientCache owner targetNonzero small 0
    different leftSmall rightSmall bottomSmall topSmall reserveSmall
  have leftMargin : (1 : Coordinate) / 2 ≤
      owner.track.initial.ambientLeftClearance.bound - displacement :=
    marginLower.trans
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct dominance.left
        displacement)
  have rightMargin : (1 : Coordinate) / 2 ≤
      owner.track.initial.ambientRightClearance.bound - displacement :=
    marginLower.trans
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct dominance.right
        displacement)
  have bottomMargin : (1 : Coordinate) / 2 ≤
      owner.track.initial.ambientBottomClearance.bound - displacement :=
    marginLower.trans
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct dominance.bottom
        displacement)
  have topMargin : (1 : Coordinate) / 2 ≤
      owner.track.initial.ambientTopClearance.bound - displacement :=
    marginLower.trans
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct dominance.top
        displacement)
  have leftMajorantLe :
      Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial source
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Winding.verticalBase owner.track.initial.box.xLower)
        Gaussian.Constants.imaginaryUnit
        (Box.Intervals.verticalInterval owner.ambient) ≤ 65536 :=
    quadraticVerticalBoundarySideMajorant_le source
      owner.track.initial.box.xLower
      (Box.Intervals.verticalInterval owner.ambient)
      budget.verticalIntervalSqLe budget.leftSqLe budget.parameterNormSqLe
  have rightMajorantLe :
      Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial source
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Winding.verticalBase owner.track.initial.box.xUpper)
        Gaussian.Constants.imaginaryUnit
        (Box.Intervals.verticalInterval owner.ambient) ≤ 65536 :=
    quadraticVerticalBoundarySideMajorant_le source
      owner.track.initial.box.xUpper
      (Box.Intervals.verticalInterval owner.ambient)
      budget.verticalIntervalSqLe budget.rightSqLe budget.parameterNormSqLe
  have bottomMajorantLe :
      Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial source
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Imaginary.horizontalBase owner.track.initial.box.yLower)
        Gaussian.Constants.horizontalDirection
        (Box.Intervals.horizontalInterval owner.ambient) ≤ 65536 :=
    quadraticHorizontalBoundarySideMajorant_le source
      owner.track.initial.box.yLower
      (Box.Intervals.horizontalInterval owner.ambient)
      budget.horizontalIntervalSqLe budget.bottomSqLe budget.parameterNormSqLe
  have topMajorantLe :
      Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial source
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Imaginary.horizontalBase owner.track.initial.box.yUpper)
        Gaussian.Constants.horizontalDirection
        (Box.Intervals.horizontalInterval owner.ambient) ≤ 65536 :=
    quadraticHorizontalBoundarySideMajorant_le source
      owner.track.initial.box.yUpper
      (Box.Intervals.horizontalInterval owner.ambient)
      budget.horizontalIntervalSqLe budget.topSqLe budget.parameterNormSqLe
  have leftFloor : quadraticAmbientTransportFloor ≤
      (ambientLeftAfterMove owner leftSmall).bound := by
    rw [ambientLeftAfterMove,
      Power.Clearance.Box.Transport.verticalClearanceAfterMove_bound]
    exact quadraticAmbientTransportFloor_le_side _ _ leftMargin
      (Basic.le_max_left _ _) leftMajorantLe
  have rightFloor : quadraticAmbientTransportFloor ≤
      (ambientRightAfterMove owner rightSmall).bound := by
    rw [ambientRightAfterMove,
      Power.Clearance.Box.Transport.verticalClearanceAfterMove_bound]
    exact quadraticAmbientTransportFloor_le_side _ _ rightMargin
      (Basic.le_max_left _ _) rightMajorantLe
  have bottomFloor : quadraticAmbientTransportFloor ≤
      (ambientBottomAfterMove owner bottomSmall).bound := by
    rw [ambientBottomAfterMove,
      Power.Clearance.Box.Transport.horizontalClearanceAfterMove_bound]
    exact quadraticAmbientTransportFloor_le_side _ _ bottomMargin
      (Basic.le_max_left _ _) bottomMajorantLe
  have topFloor : quadraticAmbientTransportFloor ≤
      (ambientTopAfterMove owner topSmall).bound := by
    rw [ambientTopAfterMove,
      Power.Clearance.Box.Transport.horizontalClearanceAfterMove_bound]
    exact quadraticAmbientTransportFloor_le_side _ _ topMargin
      (Basic.le_max_left _ _) topMajorantLe
  refine
    { initialBox := ambientCache.initialBox
      ambientBox := ambientCache.ambientBox
      clearanceFloor := ?_
      ambientLeftQuarterSq := ?_
      clearanceQuarterSq := ?_
      dominance := ambientCache.ambientClearanceDominance
      budget := ?_ }
  · rw [ambientCache.clearanceBound]
    exact le_min leftFloor (le_min rightFloor (le_min bottomFloor topFloor))
  · rw [ambientCache.ambientLeftBound]
    exact ambientLeftAfterMove_bound_le_quarter_sq owner leftSmall
  · exact ambientCache.clearanceLeAmbientLeft.trans
      (ambientCache.ambientLeftBound.le.trans
        (ambientLeftAfterMove_bound_le_quarter_sq owner leftSmall))
  · refine
      { parameterNormSqLe := targetNormSqLe
        verticalIntervalSqLe := ?_
        horizontalIntervalSqLe := ?_
        leftSqLe := ?_
        rightSqLe := ?_
        bottomSqLe := ?_
        topSqLe := ?_ }
    · rw [ambientCache.ambientBox]
      exact budget.verticalIntervalSqLe
    · rw [ambientCache.ambientBox]
      exact budget.horizontalIntervalSqLe
    · rw [ambientCache.initialBox]
      exact budget.leftSqLe
    · rw [ambientCache.initialBox]
      exact budget.rightSqLe
    · rw [ambientCache.initialBox]
      exact budget.bottomSqLe
    · rw [ambientCache.initialBox]
      exact budget.topSqLe

/-- Both executable branches retain the source box or return a certified
strict descendant. -/
theorem reservedTransport_initial_box_refines {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.clearance.bound) (reserve : Coordinate) :
    (reservedTransport owner targetNonzero small reserve).track.initial.box.Refines
      owner.track.initial.box := by
  unfold reservedTransport
  by_cases same : source = target
  · rw [dif_pos same]
    subst target
    exact Box.refines_refl _
  · rw [dif_neg same]
    dsimp only
    by_cases leftSmall :
        Data.Gaussian.Norm.Basic.normSq (source - target) <
          owner.track.initial.ambientLeftClearance.bound
    · rw [dif_pos leftSmall]
      by_cases rightSmall :
          Data.Gaussian.Norm.Basic.normSq (source - target) <
            owner.track.initial.ambientRightClearance.bound
      · rw [dif_pos rightSmall]
        by_cases bottomSmall :
            Data.Gaussian.Norm.Basic.normSq (source - target) <
              owner.track.initial.ambientBottomClearance.bound
        · rw [dif_pos bottomSmall]
          by_cases topSmall :
              Data.Gaussian.Norm.Basic.normSq (source - target) <
                owner.track.initial.ambientTopClearance.bound
          · rw [dif_pos topSmall]
            by_cases reserveSmall : reserve <
                (Riemann.RootContinuation.SquareRootContinuation.transportedOwner
                  owner.track.initial small).clearance.bound
            · rw [dif_pos reserveSmall]
              rw [ambientRoucheTransport_initial_box]
              exact Box.refines_refl _
            · rw [dif_neg reserveSmall]
              exact resultantReservedTransport_initial_box_refines owner
                targetNonzero small reserve
          · rw [dif_neg topSmall]
            exact resultantReservedTransport_initial_box_refines owner
              targetNonzero small reserve
        · rw [dif_neg bottomSmall]
          exact resultantReservedTransport_initial_box_refines owner
            targetNonzero small reserve
      · rw [dif_neg rightSmall]
        exact resultantReservedTransport_initial_box_refines owner targetNonzero
          small reserve
    · rw [dif_neg leftSmall]
      exact resultantReservedTransport_initial_box_refines owner targetNonzero
        small reserve

/-- The cheap Rouché branch and the resultant fallback both name the same
target occurrence as generic Newton continuation. -/
@[expose] def reservedTransport_generic_relation {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.clearance.bound) (reserve : Coordinate) :
    PSum
      (reservedTransport owner targetNonzero small reserve =
        owner.advance targetNonzero small)
      (DirectPresentationRelation owner targetNonzero small
        (reservedTransport owner targetNonzero small reserve)) := by
  unfold reservedTransport
  by_cases same : source = target
  · rw [dif_pos same]
    subst target
    exact PSum.inr
      { parent := owner
        genericStrictParent :=
          Riemann.RootContinuation.SquareRootContinuation.continuedTrack_initial_strict_source
            targetNonzero owner.track.initial small
        resultRefinesParent := Box.refines_refl _ }
  · rw [dif_neg same]
    dsimp only
    by_cases leftSmall :
        Data.Gaussian.Norm.Basic.normSq (source - target) <
          owner.track.initial.ambientLeftClearance.bound
    · rw [dif_pos leftSmall]
      by_cases rightSmall :
          Data.Gaussian.Norm.Basic.normSq (source - target) <
            owner.track.initial.ambientRightClearance.bound
      · rw [dif_pos rightSmall]
        by_cases bottomSmall :
            Data.Gaussian.Norm.Basic.normSq (source - target) <
              owner.track.initial.ambientBottomClearance.bound
        · rw [dif_pos bottomSmall]
          by_cases topSmall :
              Data.Gaussian.Norm.Basic.normSq (source - target) <
                owner.track.initial.ambientTopClearance.bound
          · rw [dif_pos topSmall]
            by_cases reserveSmall : reserve <
                (Riemann.RootContinuation.SquareRootContinuation.transportedOwner
                  owner.track.initial small).clearance.bound
            · rw [dif_pos reserveSmall]
              exact PSum.inr
                { parent := ambientRoucheTransport owner targetNonzero small
                    leftSmall rightSmall bottomSmall topSmall
                  genericStrictParent := by
                    rw [ambientRoucheTransport_initial_box]
                    exact Riemann.RootContinuation.SquareRootContinuation.continuedTrack_initial_strict_source
                      targetNonzero owner.track.initial small
                  resultRefinesParent := Box.refines_refl _ }
            · rw [dif_neg reserveSmall]
              exact resultantReservedTransport_generic_relation owner
                targetNonzero small reserve
          · rw [dif_neg topSmall]
            exact resultantReservedTransport_generic_relation owner
              targetNonzero small reserve
        · rw [dif_neg bottomSmall]
          exact resultantReservedTransport_generic_relation owner targetNonzero
            small reserve
      · rw [dif_neg rightSmall]
        exact resultantReservedTransport_generic_relation owner targetNonzero
          small reserve
    · rw [dif_neg leftSmall]
      exact resultantReservedTransport_generic_relation owner targetNonzero
        small reserve

/-- Fast same-box transport with only positivity reserved.  Since every exact
boundary clearance is positive, this takes the direct branch whenever all
four side resultants are nonzero. -/
@[expose] def directTransport {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.clearance.bound) : Owner target :=
  reservedTransport owner targetNonzero small 0

/-- Direct quadratic transport retains a box refining the original source owner's initial box. -/
theorem directTransport_initial_box_refines {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.clearance.bound) :
    (directTransport owner targetNonzero small).track.initial.box.Refines
      owner.track.initial.box := by
  exact reservedTransport_initial_box_refines owner targetNonzero small 0

/-- Computational branch data: either fast transport is generic transport,
or the generic Newton band is a strict descendant of its same-box direct
presentation. -/
@[expose] def directTransport_generic_relation {source target : Gaussian}
    (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.clearance.bound) :
    PSum
      (directTransport owner targetNonzero small =
        owner.advance targetNonzero small)
      (DirectPresentationRelation owner targetNonzero small
        (directTransport owner targetNonzero small)) := by
  exact reservedTransport_generic_relation owner targetNonzero small 0

attribute [irreducible] reservedTransport
  directTransport

/-- Keep the stronger of two independently certified boundary clearances on
the same rational box.

Both original certificates concern the same polynomial and box. Their pointwise inequalities bound the selected maximum,
which retains positivity from the first bound. -/
private def maxBoundaryClearance
    {polynomial : GaussianPolynomial} {box : QuadraticBox}
    (first second : BoundaryClearance polynomial box) :
    BoundaryClearance polynomial box where
  bound := max first.bound second.bound
  positive := first.positive.trans_le (Basic.le_max_left _ _)
  lower := by
    intro point boundary
    exact Basic.max_le (first.lower point boundary) (second.lower point boundary)

/-- Repackage one quadratic owner on its existing winding-one box using exact
side resultants.  Failure of any determinant check returns the original
owner, so this finite acceleration never weakens the generic construction. -/
private def strengthenQuadraticOwnerImpl {parameter : Gaussian}
    (owner : Owner parameter) : Owner parameter :=
  let box := owner.track.initial.box
  if leftNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
          parameter box.xLower ≠ 0 then
    if rightNonzero :
        SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
            parameter box.xUpper ≠ 0 then
      if bottomNonzero :
          SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
              parameter box.yLower ≠ 0 then
        if topNonzero :
            SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
                parameter box.yUpper ≠ 0 then
          let direct := directBoundaryClearance parameter box leftNonzero
            rightNonzero bottomNonzero topNonzero
          let clearance := maxBoundaryClearance
            owner.track.initial.clearance direct
          let initial : WindingOneState
              (rootPolynomial parameter) box :=
            { box := box
              refinesAmbient := Box.refines_refl box
              proper := owner.track.initial.proper
              clearance := clearance
              rawWindingFour := owner.track.initial.rawWindingFour
              ambientLeftClearance :=
                Clearance.Box.Boundary.Lines.leftOfBoundary clearance
              ambientRightClearance :=
                Clearance.Box.Boundary.Lines.rightOfBoundary clearance
              ambientBottomClearance :=
                Clearance.Box.Boundary.Lines.bottomOfBoundary clearance
              ambientTopClearance :=
                Clearance.Box.Boundary.Lines.topOfBoundary clearance }
          { parameterNonzero := owner.parameterNonzero
            ambient := box
            track := deferredTrack owner.parameterNonzero initial }
        else owner
      else owner
    else owner
  else owner

/-- Every branch of the strengthening implementation keeps the original initial box. -/
private theorem strengthenQuadraticOwnerImpl_initial_box {parameter : Gaussian}
    (owner : Owner parameter) :
    (strengthenQuadraticOwnerImpl owner).track.initial.box =
      owner.track.initial.box := by
  unfold strengthenQuadraticOwnerImpl
  dsimp only
  by_cases leftNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter owner.track.initial.box.xLower ≠ 0
  · rw [dif_pos leftNonzero]
    by_cases rightNonzero :
        SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
          parameter owner.track.initial.box.xUpper ≠ 0
    · rw [dif_pos rightNonzero]
      by_cases bottomNonzero :
          SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
            parameter owner.track.initial.box.yLower ≠ 0
      · rw [dif_pos bottomNonzero]
        by_cases topNonzero :
            SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
              parameter owner.track.initial.box.yUpper ≠ 0
        · rw [dif_pos topNonzero]
          rfl
        · rw [dif_neg topNonzero]
      · rw [dif_neg bottomNonzero]
    · rw [dif_neg rightNonzero]
  · rw [dif_neg leftNonzero]

/-- The strengthening implementation retains an ambient box refining the original ambient. -/
private theorem strengthenQuadraticOwnerImpl_ambient_refines
    {parameter : Gaussian} (owner : Owner parameter) :
    (strengthenQuadraticOwnerImpl owner).ambient.Refines owner.ambient := by
  unfold strengthenQuadraticOwnerImpl
  dsimp only
  by_cases leftNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter owner.track.initial.box.xLower ≠ 0
  · rw [dif_pos leftNonzero]
    by_cases rightNonzero :
        SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
          parameter owner.track.initial.box.xUpper ≠ 0
    · rw [dif_pos rightNonzero]
      by_cases bottomNonzero :
          SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
            parameter owner.track.initial.box.yLower ≠ 0
      · rw [dif_pos bottomNonzero]
        by_cases topNonzero :
            SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
              parameter owner.track.initial.box.yUpper ≠ 0
        · rw [dif_pos topNonzero]
          exact owner.track.initial.refinesAmbient
        · rw [dif_neg topNonzero]
          exact Box.refines_refl _
      · rw [dif_neg bottomNonzero]
        exact Box.refines_refl _
    · rw [dif_neg rightNonzero]
      exact Box.refines_refl _
  · rw [dif_neg leftNonzero]
    exact Box.refines_refl _

/-- The strengthening implementation never decreases the original boundary-clearance bound.

A failed determinant check retains the input owner. A successful check keeps the same winding-one box and selects the
maximum of its original and exact-resultant clearance bounds. -/
private theorem strengthenQuadraticOwnerImpl_clearance_le
    {parameter : Gaussian} (owner : Owner parameter) :
    owner.track.initial.clearance.bound ≤
      (strengthenQuadraticOwnerImpl owner).track.initial.clearance.bound := by
  unfold strengthenQuadraticOwnerImpl
  dsimp only
  by_cases leftNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter owner.track.initial.box.xLower ≠ 0
  · rw [dif_pos leftNonzero]
    by_cases rightNonzero :
        SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
          parameter owner.track.initial.box.xUpper ≠ 0
    · rw [dif_pos rightNonzero]
      by_cases bottomNonzero :
          SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
            parameter owner.track.initial.box.yLower ≠ 0
      · rw [dif_pos bottomNonzero]
        by_cases topNonzero :
            SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
              parameter owner.track.initial.box.yUpper ≠ 0
        · rw [dif_pos topNonzero]
          exact Basic.le_max_left _ _
        · rw [dif_neg topNonzero]
      · rw [dif_neg bottomNonzero]
    · rw [dif_neg rightNonzero]
  · rw [dif_neg leftNonzero]

/-- When all four exact side resultants are nonzero, the opaque strengthened
owner retains at least the corresponding direct resultant clearance.

The four supplied nonzero determinants select the successful original strengthening branch, whose retained maximum
dominates the exact-resultant boundary clearance. -/
private theorem strengthenQuadraticOwnerImpl_direct_clearance_le
    {parameter : Gaussian} (owner : Owner parameter)
    (leftNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter owner.track.initial.box.xLower ≠ 0)
    (rightNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter owner.track.initial.box.xUpper ≠ 0)
    (bottomNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter owner.track.initial.box.yLower ≠ 0)
    (topNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter owner.track.initial.box.yUpper ≠ 0) :
    (directBoundaryClearance parameter owner.track.initial.box leftNonzero
        rightNonzero bottomNonzero topNonzero).bound ≤
      (strengthenQuadraticOwnerImpl owner).track.initial.clearance.bound := by
  unfold strengthenQuadraticOwnerImpl
  dsimp only
  rw [dif_pos leftNonzero, dif_pos rightNonzero, dif_pos bottomNonzero,
    dif_pos topNonzero]
  exact Basic.le_max_right _ _

/-- The exact cached clearance calculation on the successful direct branch. -/
private theorem strengthenQuadraticOwnerImpl_clearance_eq_max
    {parameter : Gaussian} (owner : Owner parameter)
    (leftNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter owner.track.initial.box.xLower ≠ 0)
    (rightNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter owner.track.initial.box.xUpper ≠ 0)
    (bottomNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter owner.track.initial.box.yLower ≠ 0)
    (topNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter owner.track.initial.box.yUpper ≠ 0) :
    (strengthenQuadraticOwnerImpl owner).track.initial.clearance.bound =
      max owner.track.initial.clearance.bound
        (directBoundaryClearance parameter owner.track.initial.box leftNonzero
          rightNonzero bottomNonzero topNonzero).bound := by
  unfold strengthenQuadraticOwnerImpl
  dsimp only
  rw [dif_pos leftNonzero, dif_pos rightNonzero, dif_pos bottomNonzero,
    dif_pos topNonzero]
  rfl

/-- Successful four-resultant strengthening stores its improved boundary bound on every ambient side. -/
private theorem strengthenQuadraticOwnerImpl_ambient_clearance_eq
    {parameter : Gaussian} (owner : Owner parameter)
    (leftNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter owner.track.initial.box.xLower ≠ 0)
    (rightNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter owner.track.initial.box.xUpper ≠ 0)
    (bottomNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter owner.track.initial.box.yLower ≠ 0)
    (topNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter owner.track.initial.box.yUpper ≠ 0) :
    let strengthened := strengthenQuadraticOwnerImpl owner
    strengthened.track.initial.ambientLeftClearance.bound =
        strengthened.track.initial.clearance.bound ∧
      strengthened.track.initial.ambientRightClearance.bound =
          strengthened.track.initial.clearance.bound ∧
        strengthened.track.initial.ambientBottomClearance.bound =
            strengthened.track.initial.clearance.bound ∧
          strengthened.track.initial.ambientTopClearance.bound =
            strengthened.track.initial.clearance.bound := by
  unfold strengthenQuadraticOwnerImpl
  dsimp only
  rw [dif_pos leftNonzero, dif_pos rightNonzero, dif_pos bottomNonzero,
    dif_pos topNonzero]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The strengthening implementation preserves an existing boundary-to-ambient clearance dominance certificate. -/
private theorem strengthenQuadraticOwnerImpl_ambientClearanceDominance
    {parameter : Gaussian} (owner : Owner parameter)
    (dominance : AmbientClearanceDominance owner) :
    AmbientClearanceDominance (strengthenQuadraticOwnerImpl
      owner) := by
  unfold strengthenQuadraticOwnerImpl
  dsimp only
  by_cases leftNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter owner.track.initial.box.xLower ≠ 0
  · rw [dif_pos leftNonzero]
    by_cases rightNonzero :
        SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
          parameter owner.track.initial.box.xUpper ≠ 0
    · rw [dif_pos rightNonzero]
      by_cases bottomNonzero :
          SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
            parameter owner.track.initial.box.yLower ≠ 0
      · rw [dif_pos bottomNonzero]
        by_cases topNonzero :
            SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
              parameter owner.track.initial.box.yUpper ≠ 0
        · rw [dif_pos topNonzero]
          exact ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩
        · rw [dif_neg topNonzero]
          exact dominance
      · rw [dif_neg bottomNonzero]
        exact dominance
    · rw [dif_neg rightNonzero]
      exact dominance
  · rw [dif_neg leftNonzero]
    exact dominance

/-- Strengthening either retains the original owner or installs the displayed
deferred constructor.  This proof is also retained across the opacity boundary
below so source-associated sample replay need not guess a refiner from a box. -/
private theorem strengthenQuadraticOwnerImpl_source_or_deferred {parameter : Gaussian}
    (owner : Owner parameter) :
    strengthenQuadraticOwnerImpl owner = owner ∨
      ∃ (ambient : QuadraticBox) (initial : WindingOneState
        (rootPolynomial parameter) ambient),
        strengthenQuadraticOwnerImpl owner = ownerOfState
          owner.parameterNonzero initial := by
  by_cases leftNonzero : SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
      parameter owner.track.initial.box.xLower ≠ 0
  · by_cases rightNonzero : SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter owner.track.initial.box.xUpper ≠ 0
    · by_cases bottomNonzero : SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
          parameter owner.track.initial.box.yLower ≠ 0
      · by_cases topNonzero : SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
            parameter owner.track.initial.box.yUpper ≠ 0
        · refine Or.inr ⟨(strengthenQuadraticOwnerImpl owner).ambient,
            (strengthenQuadraticOwnerImpl owner).track.initial, ?_⟩
          unfold strengthenQuadraticOwnerImpl
          dsimp only
          rw [dif_pos leftNonzero, dif_pos rightNonzero, dif_pos bottomNonzero, dif_pos topNonzero]
          rfl
        · apply Or.inl
          unfold strengthenQuadraticOwnerImpl
          dsimp only
          rw [dif_pos leftNonzero, dif_pos rightNonzero, dif_pos bottomNonzero, dif_neg topNonzero]
      · apply Or.inl
        unfold strengthenQuadraticOwnerImpl
        dsimp only
        rw [dif_pos leftNonzero, dif_pos rightNonzero, dif_neg bottomNonzero]
    · apply Or.inl
      unfold strengthenQuadraticOwnerImpl
      dsimp only
      rw [dif_pos leftNonzero, dif_neg rightNonzero]
  · apply Or.inl
    unfold strengthenQuadraticOwnerImpl
    dsimp only
    rw [dif_neg leftNonzero]

set_option genInjectivity false in
/-- The strengthened value and the facts needed by downstream
consumers.  Keeping this as one package lets the executable implementation be
opaque to dependent conversion without hiding any certified behavior.

The same original owner indexes the retained strengthened value and its exact constructor alternative, box refinements,
quantitative clearance and ambient dominance certificates. -/
private structure Strengthening {parameter : Gaussian}
    (original : Owner parameter) where
  /-- The actual retained result of the strengthening implementation. -/ value : Owner
    parameter
  /-- The retained value is the original owner or the displayed original deferred constructor. -/ sourceOrDeferred :
    value = original ∨
    ∃ (ambient : QuadraticBox) (initial : WindingOneState
      (rootPolynomial parameter) ambient), value =
        ownerOfState original.parameterNonzero initial
  /-- The retained strengthened value keeps the original initial box. -/ initialBox : value.track.initial.box =
    original.track.initial.box
  /-- The retained strengthened ambient refines the original ambient. -/ ambientRefines : value.ambient.Refines
    original.ambient
  /-- The retained strengthened boundary bound is at least the original bound. -/ clearanceLe :
    original.track.initial.clearance.bound ≤
    value.track.initial.clearance.bound
  /-- Successful side checks make the exact direct clearance no larger than the retained strengthened bound. -/
    directClearanceLe :
    forall
      (leftNonzero :
        SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
          parameter original.track.initial.box.xLower ≠ 0)
      (rightNonzero :
        SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
          parameter original.track.initial.box.xUpper ≠ 0)
      (bottomNonzero :
        SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
          parameter original.track.initial.box.yLower ≠ 0)
      (topNonzero :
        SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
          parameter original.track.initial.box.yUpper ≠ 0),
      (directBoundaryClearance parameter original.track.initial.box
          leftNonzero rightNonzero bottomNonzero topNonzero).bound ≤
        value.track.initial.clearance.bound
  /-- Successful side checks make the retained strengthened bound exactly the maximum of original and direct clearances.
  -/ clearanceEqMax :
    forall
      (leftNonzero :
        SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
          parameter original.track.initial.box.xLower ≠ 0)
      (rightNonzero :
        SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
          parameter original.track.initial.box.xUpper ≠ 0)
      (bottomNonzero :
        SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
          parameter original.track.initial.box.yLower ≠ 0)
      (topNonzero :
        SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
          parameter original.track.initial.box.yUpper ≠ 0),
      value.track.initial.clearance.bound =
        max original.track.initial.clearance.bound
          (directBoundaryClearance parameter original.track.initial.box
            leftNonzero rightNonzero bottomNonzero topNonzero).bound
  /-- Successful side checks copy the retained strengthened boundary bound to all four ambient sides. -/
    ambientClearanceEq :
    forall
      (_leftNonzero :
        SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
          parameter original.track.initial.box.xLower ≠ 0)
      (_rightNonzero :
        SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
          parameter original.track.initial.box.xUpper ≠ 0)
      (_bottomNonzero :
        SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
          parameter original.track.initial.box.yLower ≠ 0)
      (_topNonzero :
        SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
          parameter original.track.initial.box.yUpper ≠ 0),
      value.track.initial.ambientLeftClearance.bound =
          value.track.initial.clearance.bound ∧
        value.track.initial.ambientRightClearance.bound =
            value.track.initial.clearance.bound ∧
          value.track.initial.ambientBottomClearance.bound =
              value.track.initial.clearance.bound ∧
            value.track.initial.ambientTopClearance.bound =
              value.track.initial.clearance.bound
  /-- The retained strengthened value preserves the original boundary-to-ambient dominance invariant. -/
    ambientDominance : AmbientClearanceDominance original ->
    AmbientClearanceDominance value

constructive_injectivity Strengthening

/-- The retained strengthening result behind the executable opacity boundary.

The cache stores the actual implementation value together with its constructor alternative, box refinements,
quantitative clearances and dominance proofs; clients read those certificates without reducing the constructor. -/
private opaque certifiedStrengthening {parameter : Gaussian}
    (owner : Owner parameter) : Strengthening owner :=
  { value := strengthenQuadraticOwnerImpl owner
    sourceOrDeferred := strengthenQuadraticOwnerImpl_source_or_deferred owner
    initialBox := strengthenQuadraticOwnerImpl_initial_box owner
    ambientRefines := strengthenQuadraticOwnerImpl_ambient_refines owner
    clearanceLe := strengthenQuadraticOwnerImpl_clearance_le owner
    directClearanceLe :=
      strengthenQuadraticOwnerImpl_direct_clearance_le owner
    clearanceEqMax :=
      strengthenQuadraticOwnerImpl_clearance_eq_max owner
    ambientClearanceEq :=
      strengthenQuadraticOwnerImpl_ambient_clearance_eq owner
    ambientDominance :=
      strengthenQuadraticOwnerImpl_ambientClearanceDominance owner }

/-- Preserve the existing opaque strengthening value at the public boundary. -/
def certifiedStrengtheningValue {parameter : Gaussian}
    (owner : Owner parameter) : Owner parameter :=
  (certifiedStrengthening owner).value

/-- Strengthen exact side clearances when all four determinant checks pass,
and otherwise retain the input owner. -/
@[expose] def strengthenQuadraticOwner {parameter : Gaussian}
    (owner : Owner parameter) : Owner parameter :=
  certifiedStrengtheningValue owner

/-- Expose the actual constructor alternative without evaluating or replacing
the opaque strengthened owner.  This adds proof data only. -/
theorem strengthenQuadraticOwner_source_or_deferred {parameter : Gaussian}
    (owner : Owner parameter) :
    strengthenQuadraticOwner owner = owner ∨
      ∃ (ambient : QuadraticBox) (initial : WindingOneState
        (rootPolynomial parameter) ambient),
        strengthenQuadraticOwner owner = ownerOfState
          owner.parameterNonzero initial :=
  (certifiedStrengthening owner).sourceOrDeferred

/-- The opaque strengthened owner retains exactly the original initial box. -/
theorem strengthenQuadraticOwner_initial_box {parameter : Gaussian}
    (owner : Owner parameter) :
    (strengthenQuadraticOwner owner).track.initial.box =
      owner.track.initial.box := by
  exact (certifiedStrengthening owner).initialBox

/-- The opaque strengthened owner's ambient refines the original ambient box. -/
theorem strengthenQuadraticOwner_ambient_refines {parameter : Gaussian}
    (owner : Owner parameter) :
    (strengthenQuadraticOwner owner).ambient.Refines owner.ambient :=
  (certifiedStrengthening owner).ambientRefines

/-- The finite quadratic Horner budget survives same-box strengthening.  A
successful strengthening replaces the ambient by the displayed inner box;
all other branches retain the old ambient. -/
theorem strengthenQuadraticOwner_quadraticAmbientBudget
    {parameter : Gaussian} (owner : Owner parameter)
    (budget : QuadraticAmbientBudget owner) :
    QuadraticAmbientBudget (strengthenQuadraticOwner owner) :=
      by
  have ambientRefines := strengthenQuadraticOwner_ambient_refines owner
  have verticalRefines : Refines
      (Box.Intervals.verticalInterval
        (strengthenQuadraticOwner owner).ambient)
      (Box.Intervals.verticalInterval owner.ambient) :=
    ⟨ambientRefines.2.2.1, ambientRefines.2.2.2⟩
  have horizontalRefines : Refines
      (Box.Intervals.horizontalInterval
        (strengthenQuadraticOwner owner).ambient)
      (Box.Intervals.horizontalInterval owner.ambient) :=
    ⟨ambientRefines.1, ambientRefines.2.1⟩
  refine
    { parameterNormSqLe := budget.parameterNormSqLe
      verticalIntervalSqLe :=
        (Data.Rat.Interval.Bounds.squareBound_le_of_refines
          verticalRefines).trans budget.verticalIntervalSqLe
      horizontalIntervalSqLe :=
        (Data.Rat.Interval.Bounds.squareBound_le_of_refines
          horizontalRefines).trans budget.horizontalIntervalSqLe
      leftSqLe := ?_
      rightSqLe := ?_
      bottomSqLe := ?_
      topSqLe := ?_ }
  · rw [strengthenQuadraticOwner_initial_box]
    exact budget.leftSqLe
  · rw [strengthenQuadraticOwner_initial_box]
    exact budget.rightSqLe
  · rw [strengthenQuadraticOwner_initial_box]
    exact budget.bottomSqLe
  · rw [strengthenQuadraticOwner_initial_box]
    exact budget.topSqLe

/-- The opaque strengthened owner retains at least the original boundary-clearance bound. -/
theorem strengthenQuadraticOwner_clearance_le
    {parameter : Gaussian} (owner : Owner parameter) :
    owner.track.initial.clearance.bound ≤
      (strengthenQuadraticOwner owner).track.initial.clearance.bound := by
  exact (certifiedStrengthening owner).clearanceLe

/-- Same-box strengthening preserves boundary-to-ambient dominance on every
executable branch. -/
theorem strengthenQuadraticOwner_ambientClearanceDominance_of
    {parameter : Gaussian} (owner : Owner parameter)
    (dominance : AmbientClearanceDominance owner) :
    AmbientClearanceDominance (strengthenQuadraticOwner owner)
      :=
  (certifiedStrengthening owner).ambientDominance dominance

/-- The exact four-side resultant clearance is available through the opaque
strengthening interface.  This avoids reevaluating the strengthening
implementation merely to use its quantitative improvement. -/
theorem directBoundaryClearance_le_strengthenQuadraticOwner
    {parameter : Gaussian} (owner : Owner parameter)
    (leftNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter owner.track.initial.box.xLower ≠ 0)
    (rightNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter owner.track.initial.box.xUpper ≠ 0)
    (bottomNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter owner.track.initial.box.yLower ≠ 0)
    (topNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter owner.track.initial.box.yUpper ≠ 0) :
    (directBoundaryClearance parameter owner.track.initial.box leftNonzero
        rightNonzero bottomNonzero topNonzero).bound ≤
      (strengthenQuadraticOwner owner).track.initial.clearance.bound := by
  exact (certifiedStrengthening owner).directClearanceLe leftNonzero
    rightNonzero bottomNonzero topNonzero

/-- Exact rational clearance exposed by the opaque strengthening cache. -/
theorem strengthenQuadraticOwner_clearance_eq_max
    {parameter : Gaussian} (owner : Owner parameter)
    (leftNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter owner.track.initial.box.xLower ≠ 0)
    (rightNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter owner.track.initial.box.xUpper ≠ 0)
    (bottomNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter owner.track.initial.box.yLower ≠ 0)
    (topNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter owner.track.initial.box.yUpper ≠ 0) :
    (strengthenQuadraticOwner owner).track.initial.clearance.bound =
      max owner.track.initial.clearance.bound
        (directBoundaryClearance parameter owner.track.initial.box leftNonzero
          rightNonzero bottomNonzero topNonzero).bound := by
  exact (certifiedStrengthening owner).clearanceEqMax leftNonzero rightNonzero
    bottomNonzero topNonzero

/-- A successful same-box strengthening caches its improved boundary
clearance on all four ambient sides as well.  Subsequent transport proofs can
therefore carry one numerical reserve instead of reopening the strengthening
implementation. -/
theorem strengthenQuadraticOwner_ambient_clearance_eq
    {parameter : Gaussian} (owner : Owner parameter)
    (leftNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter owner.track.initial.box.xLower ≠ 0)
    (rightNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter owner.track.initial.box.xUpper ≠ 0)
    (bottomNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter owner.track.initial.box.yLower ≠ 0)
    (topNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter owner.track.initial.box.yUpper ≠ 0) :
    let strengthened := strengthenQuadraticOwner owner
    strengthened.track.initial.ambientLeftClearance.bound =
        strengthened.track.initial.clearance.bound ∧
      strengthened.track.initial.ambientRightClearance.bound =
          strengthened.track.initial.clearance.bound ∧
        strengthened.track.initial.ambientBottomClearance.bound =
            strengthened.track.initial.clearance.bound ∧
          strengthened.track.initial.ambientTopClearance.bound =
            strengthened.track.initial.clearance.bound := by
  exact (certifiedStrengthening owner).ambientClearanceEq leftNonzero
    rightNonzero bottomNonzero topNonzero

open Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance in
/-- A successful four-resultant strengthening restores the finite
boundary-to-ambient dominance invariant, independently of the input owner's
ambient certificates. -/
theorem strengthenQuadraticOwner_ambientClearanceDominance
    {parameter : Gaussian} (owner : Owner parameter)
    (leftNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter owner.track.initial.box.xLower ≠ 0)
    (rightNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter owner.track.initial.box.xUpper ≠ 0)
    (bottomNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter owner.track.initial.box.yLower ≠ 0)
    (topNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter owner.track.initial.box.yUpper ≠ 0) :
    AmbientClearanceDominance (strengthenQuadraticOwner owner)
      := by
  rcases strengthenQuadraticOwner_ambient_clearance_eq owner leftNonzero
    rightNonzero bottomNonzero topNonzero with
    ⟨leftEq, rightEq, bottomEq, topEq⟩
  exact
    { left := le_of_eq leftEq.symm
      right := le_of_eq rightEq.symm
      bottom := le_of_eq bottomEq.symm
      top := le_of_eq topEq.symm }

attribute [irreducible] strengthenQuadraticOwner

end Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance

end
