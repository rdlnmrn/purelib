module
import Purelib.Riemann.Integration.LegendreModularMonodromy
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator
public import Purelib.Approximation.Gaussian.Affine.Integral
import Purelib.Approximation.Gaussian.Arithmetic.Mul
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Process.Apart.Possible
public import Purelib.Approximation.Gaussian.Process.Imaginary.Positive.Basic
public import Purelib.Data.Gaussian.Affine.Integral.Bounds
import Purelib.Data.Gaussian.Cast
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Inverse.Right
import Init.Data.Int.Basic
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Based
import Purelib.Approximation.Gaussian.Process.Apart
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Matrix.Operational.Integral.Action
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic

open Purelib.Approximation.Gaussian.Process.Imaginary.Positive.Basic (PositiveEnclosure)
open Purelib.LinearAlgebra.Matrix.Basic (IntegralMatrix)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Affine

open Purelib.Approximation.Gaussian.Arithmetic

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.FractionalAction.Integral

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum

open Purelib.Approximation.Gaussian.Process.Apart

open Purelib.Approximation.Gaussian.Process.Imaginary

open Purelib.Data.Gaussian

open Purelib.Data.Gaussian.Affine

open Purelib.LinearAlgebra.Matrix

open Purelib.LinearAlgebra.Matrix.Inverse

section
@[expose] public section

/-!
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
-/

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Positive
open Purelib.Riemann.Integration.LegendreModularMonodromy hiding IntegralMatrix
open Purelib.Approximation.Gaussian.Division.Prepared (DenominatorPreparation)

/-- Candidate apartness for every nonzero row, obtained directly from the single retained positivity enclosure. -/
def affineApart {tau :
  Coherent.CoherentNamed} (certificate : PositiveEnclosure tau)
    (a b : Int) (nonzero : a ≠ 0 ∨ b ≠ 0) :
    Possible.PossibleApart (Integral.affine a b certificate.based).name.process where
  lowerSq := Integral.Bounds.rowLower a b certificate.lower
  positive := Integral.Bounds.rowLower_positive a b certificate.lower certificate.positive nonzero
  lower := by
    intro state value possible
    rcases possible with ⟨x, y, hx, hy, rfl⟩
    rcases hy with ⟨z, w, hz, hw, rfl⟩
    change x = Cast.integralGaussian a at hx
    change z = Cast.integralGaussian b at hz
    subst x
    subst z
    exact Integral.Bounds.rowLower_le a b certificate.lower w certificate.positive
      (certificate.possible_lower _ hw)

/-- The expanded affine program denotes the same row as the public matrix action. Rebasing occurs only at the supplied
positive enclosure. -/
def denominator_affine {tau :
  Coherent.CoherentNamed}
    (certificate : PositiveEnclosure tau) (matrix : IntegralMatrix) :
    Gaussian.Equivalence.NamedEquivalent (fractionalDenominator matrix tau).name
      (Integral.affine (matrix 0 0) (matrix 0 1) certificate.based).name := by
  have expanded := matrixAction_row_two matrix (fractionalVector tau) 0
  rw [fractionalVector_zero, fractionalVector_one] at expanded
  exact NamedEquivalent.trans expanded
    (Congruence.coherentAdd_respects _ _ _ _
      (Mul.coherentMul_one_right _)
      (Congruence.coherentMul_respects _ _ _ _
        (NamedEquivalent.refl _)
        (tau.basedEquivalent certificate.state)))

/-- Guaranteed finite denominator preparation for any nonzero integral row. The executable apartifier requests squared
radius below `rowLower / 12`; its resulting whole-ball bound is `rowLower / 8`. -/
def prepare {tau :
  Coherent.CoherentNamed} (certificate : PositiveEnclosure tau)
    (matrix : IntegralMatrix) (nonzero : matrix 0 0 ≠ 0 ∨ matrix 0 1 ≠ 0) :
    DenominatorPreparation (fractionalDenominator matrix tau) :=
  let ready := DenominatorPreparation.ofPossibleApart
    (Integral.affine (matrix 0 0) (matrix 0 1) certificate.based)
    (affineApart certificate (matrix 0 0) (matrix
      0 1) nonzero)
  { prepared := ready.prepared
    apart := ready.apart
    equivalent := NamedEquivalent.trans
      (denominator_affine certificate matrix)
        ready.equivalent }

/-- The prescribed finite preparation retains an explicit whole-ball lower bound, including for negative coefficients
and constant rows. -/
theorem prepare_lowerSq {tau :
  Coherent.CoherentNamed}
    (certificate : PositiveEnclosure tau) (matrix : IntegralMatrix)
    (nonzero : matrix 0 0 ≠ 0 ∨ matrix 0 1 ≠ 0) :
    (prepare certificate matrix
      nonzero).apart.certificate.lowerSq =
      Integral.Bounds.rowLower (matrix 0 0) (matrix 0 1) certificate.lower / 8 := rfl
end Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Positive

end

section
@[expose] public section

/-!
# Denominator preparation survives fractional composition

A preparation provider for all invertible integral matrices can be carried
through a prepared fractional action. An outer denominator is represented as
the quotient of the combined and inner denominators. Both are already apart;
one retained base state supplies a uniform upper bound for the divisor.
-/

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Positive

/-- Prepare every invertible integral matrix from one retained positive imaginary enclosure.

The inverse certificate proves each denominator row is nonzero; the positive enclosure then supplies its explicit finite
apartification bound. -/
def ofPositiveEnclosure {tau :
  Coherent.CoherentNamed}
    (positive : PositiveEnclosure tau) : Preparation.Basic.Provider tau :=
  fun matrix inverse => prepare positive matrix
    (Right.row_nonzero_of_inverse _ _ inverse.identity)
end Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Positive

end
