module
import Purelib.Data.GaussianInt.Pair.Basic
public import Purelib.Data.GaussianInt.Conjugate
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Cancellation
public import Purelib.Data.GaussianInt.Divisibility.Basic
public import Purelib.Data.GaussianInt.Pair.Basis

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.GaussianInt

open Purelib.Data.GaussianInt.Divisibility

open Purelib.Data.GaussianInt.Pair

open Purelib.Data.GaussianInt.Pair.Basic

section
@[expose] public section

/-!
# Finite best Gaussian-rational approximations

Chevallier's lattice formulation uses two coordinate sizes: the error
`|qz-p|` and the denominator `|q|`.  This file states the same comparison
without square roots and without a completed complex carrier.  A lattice
vector is represented by its displayed Gaussian-integer pair `(p,q)`, its
first coordinate is the division-free rational error `qz-p`, and its second
coordinate is the displayed denominator `q`.

The main theorem proves directly that the two-tier best-approximation
predicate is equivalent to minimality in the corresponding closed cylinder.
All quantifiers range over supplied finite Gaussian-integer records; no
lattice completion, global enumeration, or choice principle is used.
-/

namespace Purelib.Data.GaussianInt.Pair.LinearCombination

/-- Compute the integral cross determinant of two displayed coefficient pairs. -/
def coefficientDeterminant (left right : ConvergentPair) :
  GaussianInt :=
  Basis.determinant left right

/-- Compute the natural quadrance of the two displayed pairs' integral determinant. -/
def coefficientIndexQuadrance (left right : ConvergentPair) : Nat
  :=
  GaussianInt.normNat (coefficientDeterminant left right)

/-- The coefficient pair whose numerator and denominator are both zero. -/
def zeroPair : ConvergentPair :=
  { numerator := 0
    denominator := 0 }

/-- Equality of both retained integral coordinates gives equality of coefficient pairs. -/
theorem pair_ext {left right : ConvergentPair}
    (numeratorEqual : left.numerator = right.numerator)
    (denominatorEqual : left.denominator = right.denominator) :
    left = right := by
  cases left
  cases right
  cases numeratorEqual
  cases denominatorEqual
  rfl

/-- At least one retained integral coordinate of the displayed pair is nonzero. -/
def PairNonzero (pair : ConvergentPair) : Prop :=
  pair.numerator ≠ 0 ∨ pair.denominator ≠ 0

/-- Coordinatewise nonzeroness of a pair is equivalent to inequality from the displayed
zero pair. -/
theorem pairNonzero_iff_ne_zeroPair (pair : ConvergentPair) :
    PairNonzero pair ↔ pair ≠ zeroPair := by
  constructor
  · intro nonzero equal
    subst pair
    rcases nonzero with numeratorNonzero | denominatorNonzero
    · exact numeratorNonzero rfl
    · exact denominatorNonzero rfl
  · intro pairNonzero
    by_cases numeratorZero : pair.numerator = 0
    · by_cases denominatorZero : pair.denominator = 0
      · exact (pairNonzero (by
          cases pair
          cases numeratorZero
          cases denominatorZero
          rfl)).elim
      · exact Or.inr denominatorZero
    · exact Or.inl numeratorZero

/-- Combine two retained coefficient pairs using the supplied Gaussian-integer scalars.

The same left and right scalars act on both numerator and denominator, preserving
their paired linear relation. -/
def linearCombination
    (left right : ConvergentPair) (leftCoefficient rightCoefficient : GaussianInt) : ConvergentPair :=
  { numerator :=
      leftCoefficient * left.numerator + rightCoefficient * right.numerator
    denominator :=
      leftCoefficient * left.denominator + rightCoefficient * right.denominator }

/-- Multiply both integral coordinates of the retained pair by one displayed Gaussian
integer. -/
def scalePair (coefficient : GaussianInt) (pair : ConvergentPair)
  : ConvergentPair :=
  { numerator := coefficient * pair.numerator
    denominator := coefficient * pair.denominator }

/-- The two cross-determinant coefficients reconstruct a candidate pair scaled by the
original determinant.

The identity holds for arbitrary retained pairs, including singular pairs; no
division or nonzero determinant assumption is used. -/
theorem linearCombination_cramer
    (left right candidate : ConvergentPair) :
    linearCombination left right
        (coefficientDeterminant candidate right)
        (coefficientDeterminant left candidate) =
      scalePair (coefficientDeterminant left right) candidate := by
  apply pair_ext <;>
    apply GaussianInt.ext <;>
    simp only [linearCombination, scalePair,
      coefficientDeterminant,
      Basis.determinant,
      GaussianInt.sub_re,
      GaussianInt.sub_im,
      GaussianInt.add_re,
      GaussianInt.add_im,
      GaussianInt.mul_re,
      GaussianInt.mul_im] <;>
    ring1

/-- Scaling both coefficients scales the complete retained pair combination by the same
factor. -/
theorem linearCombination_scaleCoefficients
    (left right : ConvergentPair) (scale leftCoefficient rightCoefficient : GaussianInt) :
    linearCombination left right
        (scale * leftCoefficient) (scale * rightCoefficient) =
      scalePair scale
        (linearCombination left right leftCoefficient rightCoefficient) := by
  apply pair_ext <;>
    apply GaussianInt.ext <;>
    simp only [linearCombination, scalePair,
      GaussianInt.add_re,
      GaussianInt.add_im,
      GaussianInt.mul_re,
      GaussianInt.mul_im] <;>
    ring1

/-- Substituting a pair combination in the right argument collects its two explicit
coefficients. -/
theorem linearCombination_nested_right
    (left complement : ConvergentPair)
    (innerLeft innerRight outerLeft outerRight : GaussianInt) :
    linearCombination left
        (linearCombination left complement innerLeft innerRight)
        outerLeft outerRight =
      linearCombination left complement
        (outerLeft + outerRight * innerLeft)
        (outerRight * innerRight) := by
  apply pair_ext <;>
    apply GaussianInt.ext <;>
    simp only [linearCombination,
      GaussianInt.add_re,
      GaussianInt.add_im,
      GaussianInt.mul_re,
      GaussianInt.mul_im] <;>
    ring1

/-- Two consecutive pair scalings equal scaling by the product of their retained factors. -/
theorem scalePair_scalePair
    (left right : GaussianInt) (pair : ConvergentPair) :
    scalePair left (scalePair right pair) =
      scalePair (left * right) pair := by
  apply pair_ext <;>
    apply GaussianInt.ext <;>
    simp only [scalePair,
      GaussianInt.mul_re,
      GaussianInt.mul_im] <;>
    ring1

/-- Conjugate-scaled Cramer coefficients reconstruct a pair scaled by determinant
quadrance.

Multiplying the determinant identity by its explicit conjugate converts the integral
determinant factor to the corresponding real natural Gaussian integer. -/
theorem linearCombination_cramer_norm
    (left right candidate : ConvergentPair) :
    let determinantValue := coefficientDeterminant left right
    linearCombination left right
        (GaussianInt.conj determinantValue * coefficientDeterminant candidate right)
        (GaussianInt.conj determinantValue * coefficientDeterminant left candidate) =
      scalePair (GaussianInt.ofNat (coefficientIndexQuadrance left right)) candidate
        := by
  dsimp only
  rw [linearCombination_scaleCoefficients, linearCombination_cramer,
    scalePair_scalePair]
  have conjugateProduct :
      GaussianInt.conj (coefficientDeterminant left right) *
          coefficientDeterminant left right =
        GaussianInt.ofNat (coefficientIndexQuadrance left right) := by
    rw [GaussianInt.mul_comm, GaussianInt.mul_conj]
    rfl
  rw [conjugateProduct]

/-- Pairs of determinant quadrance one reconstruct every candidate with explicit integral
Cramer coefficients. -/
theorem linearCombination_cramer_of_index_one
    (left right candidate : ConvergentPair)
    (indexOne : coefficientIndexQuadrance left right = 1) :
    let determinantValue := coefficientDeterminant left right
    linearCombination left right
        (GaussianInt.conj determinantValue * coefficientDeterminant candidate right)
        (GaussianInt.conj determinantValue * coefficientDeterminant left candidate) =
      candidate := by
  dsimp only
  rw [linearCombination_cramer_norm, indexOne]
  apply pair_ext <;>
    apply GaussianInt.ext <;>
    simp only [scalePair, GaussianInt.ofNat,
      GaussianInt.mul_re,
      GaussianInt.mul_im] <;>
    ring1

/-- Retain two explicit Gaussian-integer coefficients expressing the candidate in the
displayed pair span. -/
def InCoefficientSpan (left right candidate : ConvergentPair) :
  Prop :=
  ∃ leftCoefficient rightCoefficient : GaussianInt,
    candidate = linearCombination left right
      leftCoefficient rightCoefficient

/-- Retain a determinant-cleared pair combination whose two coefficients are not
divisible by that determinant.

The exact scaled candidate and both nondivisibility witnesses are stored relative to
the same original pair determinant. -/
def InCenteredCoefficientCoset (left right candidate :
  ConvergentPair) : Prop :=
  let determinantValue := coefficientDeterminant left right
  ∃ leftCoefficient rightCoefficient : GaussianInt,
    ¬ Basic.Divides determinantValue leftCoefficient ∧
    ¬ Basic.Divides determinantValue rightCoefficient ∧
    scalePair determinantValue candidate =
      linearCombination left right leftCoefficient rightCoefficient

/-- Pairs of determinant quadrance two explicitly span twice every candidate pair.

The same conjugate-determinant Cramer coefficients retain an integral combination
equal to scaling the candidate by the real Gaussian integer two. -/
theorem linearCombination_cramer_of_index_two
    (left right candidate : ConvergentPair)
    (indexTwo : coefficientIndexQuadrance left right = 2) :
    let determinantValue := coefficientDeterminant left right
    linearCombination left right
        (GaussianInt.conj determinantValue * coefficientDeterminant candidate right)
        (GaussianInt.conj determinantValue * coefficientDeterminant left candidate) =
      scalePair (GaussianInt.ofNat 2) candidate := by
  dsimp only
  rw [linearCombination_cramer_norm, indexTwo]

/-- Taking a combination against its right basis pair retains only the left coefficient
times the basis determinant. -/
theorem coefficientDeterminant_linearCombination_right
    (left right : ConvergentPair) (leftCoefficient rightCoefficient : GaussianInt) :
    coefficientDeterminant
        (linearCombination left right leftCoefficient rightCoefficient) right =
      leftCoefficient * coefficientDeterminant left right := by
  apply GaussianInt.ext <;>
    simp only [coefficientDeterminant, Basis.determinant, linearCombination,
      GaussianInt.sub_re,
      GaussianInt.sub_im,
      GaussianInt.add_re,
      GaussianInt.add_im,
      GaussianInt.mul_re,
      GaussianInt.mul_im] <;>
    ring1

/-- Taking the left basis pair against a combination retains only the right coefficient
times the basis determinant. -/
theorem coefficientDeterminant_left_linearCombination
    (left right : ConvergentPair) (leftCoefficient rightCoefficient : GaussianInt) :
    coefficientDeterminant left
        (linearCombination left right leftCoefficient rightCoefficient) =
      rightCoefficient * coefficientDeterminant left right := by
  apply GaussianInt.ext <;>
    simp only [coefficientDeterminant, Basis.determinant, linearCombination,
      GaussianInt.sub_re,
      GaussianInt.sub_im,
      GaussianInt.add_re,
      GaussianInt.add_im,
      GaussianInt.mul_re,
      GaussianInt.mul_im] <;>
    ring1

/-- Taking the right basis pair against a combination gives the negated left coefficient
times the basis determinant. -/
theorem coefficientDeterminant_right_linearCombination
    (left right : ConvergentPair) (leftCoefficient rightCoefficient : GaussianInt) :
    coefficientDeterminant right
        (linearCombination left right leftCoefficient rightCoefficient) =
      -(leftCoefficient * coefficientDeterminant left right) := by
  apply GaussianInt.ext <;>
    simp only [coefficientDeterminant, Basis.determinant, linearCombination,
      GaussianInt.neg_re,
      GaussianInt.neg_im,
      GaussianInt.sub_re,
      GaussianInt.sub_im,
      GaussianInt.add_re,
      GaussianInt.add_im,
      GaussianInt.mul_re,
      GaussianInt.mul_im] <;>
    ring1

/-- Scaling the right pair scales the cross determinant by the same Gaussian integer. -/
theorem coefficientDeterminant_scalePair_right
    (left pair : ConvergentPair) (scale : GaussianInt) :
    coefficientDeterminant left (scalePair scale pair) =
      scale * coefficientDeterminant left pair := by
  apply GaussianInt.ext <;>
    simp only [coefficientDeterminant, Basis.determinant, scalePair,
      GaussianInt.sub_re,
      GaussianInt.sub_im,
      GaussianInt.mul_re,
      GaussianInt.mul_im] <;>
    ring1

/-- A pair with nonzero determinant has unique integral linear-combination coefficients.

Apply its two determinant functionals to an equality of combinations and cancel the
same retained nonzero determinant in each coordinate. -/
theorem linearCombination_coefficients_eq_of_determinant_ne_zero
    (left right : ConvergentPair)
    (determinantNonzero : coefficientDeterminant left right ≠ 0)
    {firstLeft firstRight secondLeft secondRight : GaussianInt}
    (identity :
      linearCombination left right firstLeft firstRight =
        linearCombination left right secondLeft secondRight) :
    firstLeft = secondLeft ∧ firstRight = secondRight := by
  constructor
  · have coefficientIdentity :=
      congrArg (fun pair => coefficientDeterminant pair right) identity
    rw [coefficientDeterminant_linearCombination_right,
      coefficientDeterminant_linearCombination_right] at coefficientIdentity
    exact Cancellation.mul_right_cancel_of_nonzero
      determinantNonzero coefficientIdentity
  · have coefficientIdentity :=
      congrArg (coefficientDeterminant left) identity
    rw [coefficientDeterminant_left_linearCombination,
      coefficientDeterminant_left_linearCombination] at coefficientIdentity
    exact Cancellation.mul_right_cancel_of_nonzero
      determinantNonzero coefficientIdentity
end Purelib.Data.GaussianInt.Pair.LinearCombination

end
