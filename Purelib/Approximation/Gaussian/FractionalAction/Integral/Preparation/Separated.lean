module
public import Purelib.Approximation.Gaussian.Affine.Integral
import Purelib.Approximation.Gaussian.Arithmetic.Mul
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Data.Gaussian.Cast
import Purelib.LinearAlgebra.Matrix.Inverse.Right

public import Purelib.Approximation.Gaussian.Process.Imaginary.Separation.Basic
public import Purelib.Data.Gaussian.Affine.Integral.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Riemann.Integration.LegendreModularMonodromy
import Init.Data.Int.Basic
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Based
import Purelib.Approximation.Gaussian.Process.Apart
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Matrix.Operational.Integral.Action
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Matrix.Basic

open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Process.Imaginary (Separation)

open Purelib

open Purelib.Approximation.Gaussian.Affine

open Purelib.Approximation.Gaussian.Arithmetic

open Purelib.Approximation.Gaussian.FractionalAction.Integral

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum

open Purelib.Approximation.Gaussian.Process.Apart

open Purelib.Approximation.Gaussian.Process.Imaginary

open Purelib.Data.Gaussian

open Purelib.Data.Gaussian.Affine

open Purelib.LinearAlgebra.Matrix.Inverse

open Purelib.Approximation

section
@[expose] public section

/-!
# Word-denominator preparation from unsigned imaginary separation

A positive squared imaginary-coordinate gap on retained candidates suffices
for every nonzero integral row. No sign is chosen and no upper-half-plane
claim is made. The existing apartifier and fractional-composition provider
then prepare arbitrary words in either half-plane.
-/

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Separated
open Purelib.Approximation.Gaussian.Division.Prepared (DenominatorPreparation)

open Purelib.Riemann.Integration.LegendreModularMonodromy
open Purelib.Data.Gaussian.Cast (integralGaussian)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Approximation.Gaussian.Affine.Integral (affine)
open Purelib.Data.Gaussian.Affine.Integral.Bounds (rowLower rowLower_positive)
open Purelib.Data.Gaussian.Basic.Canonical

/-- Every nonzero integral affine row is apart on an unsigned imaginary-separated input.

The retained squared gap gives a positive row norm bound for every candidate at the based process, including rows with
negative coefficients. -/
def affineApart {tau :
  CoherentNamed} (certificate : Separation tau)
    (a b : Int) (nonzero : a ≠ 0 ∨ b ≠ 0) :
    Possible.PossibleApart (Integral.affine a b certificate.based).name.process where
  lowerSq := Integral.Bounds.rowLower a b certificate.gap
  positive := Integral.Bounds.rowLower_positive a b certificate.gap certificate.positive nonzero
  lower := by
    intro state value possible
    rcases possible with ⟨x, y, hx, hy, rfl⟩
    rcases hy with ⟨z, w, hz, hw, rfl⟩
    change x = Cast.integralGaussian a at hx
    change z = Cast.integralGaussian b at hz
    subst x
    subst z
    exact Integral.Bounds.rowLower_le_of_squared a b certificate.gap w (certificate.possible_squared_lower _ hw)

/-- The matrix denominator agrees operationally with the affine row at the retained separation state. -/
def denominator_affine {tau :
  CoherentNamed} (certificate : Separation tau) (matrix
      :
    IntegralMatrix) :
    NamedEquivalent (fractionalDenominator matrix tau).name
      (Integral.affine (matrix 0 0) (matrix 0 1) certificate.based).name := by
  have expanded := matrixAction_row_two matrix (fractionalVector tau) 0
  rw [fractionalVector_zero, fractionalVector_one] at expanded
  exact NamedEquivalent.trans expanded
    (Congruence.coherentAdd_respects _ _ _ _
      (Mul.coherentMul_one_right _)
      (Congruence.coherentMul_respects _ _ _ _
        (NamedEquivalent.refl _)
        (tau.basedEquivalent certificate.state)))

/-- Prepare a nonzero denominator row from retained unsigned imaginary separation.

The finite apartifier consumes the row lower bound, and the result retains equivalence to the original fractional
denominator without choosing an imaginary sign. -/
def prepare {tau :
  CoherentNamed}
  (certificate : Separation tau)
    (matrix : IntegralMatrix) (nonzero : matrix 0 0 ≠ 0 ∨ matrix 0 1 ≠ 0) :
    DenominatorPreparation (fractionalDenominator matrix tau) :=
  let prepared := DenominatorPreparation.ofPossibleApart
    (Integral.affine (matrix 0 0) (matrix 0 1) certificate.based)
    (affineApart certificate (matrix 0 0) (matrix
      0 1) nonzero)
  { prepared := prepared.prepared
    apart := prepared.apart
    equivalent := NamedEquivalent.trans
      (denominator_affine certificate matrix)
        prepared.equivalent }

/-- The prepared whole-ball lower bound is exactly one eighth of the retained affine row bound. -/
theorem prepare_lowerSq {tau :
  CoherentNamed} (certificate : Separation tau)
    (matrix : IntegralMatrix) (nonzero : matrix 0 0 ≠ 0 ∨ matrix 0 1 ≠ 0) :
    (prepare certificate matrix
      nonzero).apart.certificate.lowerSq =
      Integral.Bounds.rowLower (matrix 0 0) (matrix 0 1) certificate.gap / 8 := rfl

/-- Construct an all-matrix denominator provider from unsigned imaginary separation.

Each inverse certificate proves the relevant matrix row is nonzero, allowing the same retained separation certificate to
prepare it. -/
def provider {tau :
  CoherentNamed}
  (certificate : Separation tau) :
    Preparation.Basic.Provider tau :=
  fun matrix inverse => prepare certificate
    matrix
    (Right.row_nonzero_of_inverse _ _ inverse.identity)

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Separated

end
