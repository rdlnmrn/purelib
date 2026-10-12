module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.SquareClass.Basic
import Purelib.Algebra.Quaternion.Projective.Basic
public import Purelib.Algebra.Quaternion.Projective.SquareClass
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.LinearAlgebra.Coordinates3.Vector
public import Purelib.NumberTheory.FourSquares.Rational
import Purelib.NumberTheory.SquareClass.Rational.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Algebra.Field.SquareClass.Basic

open Purelib.Algebra.Field.SumsOfSquares.Four

open Purelib.Algebra.Quaternion.Projective

open Purelib.Algebra.Quaternion.Projective.Basic

open Purelib.Data.Rat

open Purelib.NumberTheory.FourSquares.Rational.TheoremSixtyTwo

open Purelib.NumberTheory.FourSquares

open Purelib.NumberTheory.SquareClass.Rational.Basic.TheoremSixtyTwo

section
@[expose] public section

/-!
# Rational rotations, Theorem 62: constructive surjectivity boundary

The paper invokes Lagrange's four-square theorem to represent every positive
rational square class.  The upstream theorem is not in the paper-facing
dependency graph: its proof uses classical finite-field and cardinality
infrastructure excluded by this repository.

This module supplies that obligation by an explicitly finite prime-residue
search, Lagrange descent, bounded proper-factor recursion, and Euler products.
The algorithm returns four natural numbers together with their checked
equation.  From it the paper's rational construction is performed in finite
coordinates.  Conversely, every non-null rational proportion is proved to
have strictly positive norm.
-/

namespace Purelib.Algebra.Quaternion.Projective.Rational.Surjectivity

namespace TheoremSixtyTwo

/-- Construct a non-null rational quaternion proportion for a positive square-class representative.

The supplied executable four-square algorithm produces retained rational coordinates whose norm realizes the target
value. -/
def preimage (algorithm :
  NaturalFourSquareAlgorithm)
    (target : PositiveSquareClassRepresentative) : Basic.NonNullProportion Fraction.Rational :=
  (Rational.TheoremSixtyTwo.rationalRepresentation algorithm target).proportion target.representative

open Purelib.Algebra.Quaternion.Projective.Rational in
/-- The constructed rational preimage has quadrance-class value equal to its positive target.

The equality uses the exact coordinates produced by the supplied four-square algorithm. -/
theorem preimage_quadranceClass
  (algorithm : NaturalFourSquareAlgorithm)
    (target : PositiveSquareClassRepresentative) :
    (SquareClass.NonNullProportion.quadranceClass (preimage algorithm target)).value =
      target.representative.value :=
  FourSquareRepresentation.realizes_quadranceClass target.representative
    (Rational.TheoremSixtyTwo.rationalRepresentation algorithm target)

/-- Every rational quaternion proportion has nonnegative norm.

Its norm is the sum of four nonnegative displayed coordinate squares. -/
theorem proportion_norm_nonnegative
  (proportion : Proportion Fraction.Rational) :
    0 ≤ proportion.norm := open Purelib.Data.Rat.Fraction in open Purelib.LinearAlgebra.Coordinates3 in by
  have scalarNonnegative : 0 ≤ proportion.scalar ^ 2 :=
    Order.Arithmetic.sq_nonneg_direct proportion.scalar
  have tNonnegative : 0 ≤ proportion.vector.t * proportion.vector.t := by
    simpa only [pow_two] using
      Order.Arithmetic.sq_nonneg_direct proportion.vector.t
  have rNonnegative : 0 ≤ proportion.vector.r * proportion.vector.r := by
    simpa only [pow_two] using
      Order.Arithmetic.sq_nonneg_direct proportion.vector.r
  have sNonnegative : 0 ≤ proportion.vector.s * proportion.vector.s := by
    simpa only [pow_two] using
      Order.Arithmetic.sq_nonneg_direct proportion.vector.s
  unfold Proportion.norm Vector.quadrance Vector.dot
  exact add_nonneg scalarNonnegative
    (add_nonneg (add_nonneg tNonnegative rNonnegative) sNonnegative)

open Purelib.Algebra.Quaternion.Projective.Rational in
/-- Every non-null rational quaternion proportion has strictly positive norm.

The retained nonzero certificate strengthens nonnegativity of its four-square norm. -/
theorem
  nonNullProportion_norm_positive
    (proportion : Basic.NonNullProportion Fraction.Rational) :
    0 < proportion.toProportion.norm :=
  lt_of_le_of_ne (proportion_norm_nonnegative proportion.toProportion)
    proportion.normNonzero.symm

/-- A square-class representative is equivalent to the norm of a non-null rational proportion.

The existential retains the proportion and the explicit nonzero square factor witnessing equivalence. -/
def InQuadranceClassImage (target :
  SquareClassRepresentative Fraction.Rational) : Prop :=
  ∃ proportion : Basic.NonNullProportion Fraction.Rational,
    (SquareClass.NonNullProportion.quadranceClass proportion).Equivalent target

open Purelib.Algebra.Quaternion.Projective.Rational
/-- The rational quadrance-class image consists exactly of positive representatives.

A supplied executable four-square algorithm constructs a preimage for the positive direction. -/
theorem
  inQuadranceClassImage_iff_positive
    (algorithm : NaturalFourSquareAlgorithm)
    (target : SquareClassRepresentative Fraction.Rational) :
    InQuadranceClassImage target ↔ 0 < target.value := open Purelib.Data.Rat.Fraction in by
  constructor
  · rintro ⟨proportion, factor, factorNonzero, targetValue⟩
    have factorSquareNonzero : factor ^ 2 ≠ 0 := by
      simpa only [pow_two] using
        Fraction.Field.mul_ne_zero_direct factorNonzero
          factorNonzero
    have factorSquarePositive : 0 < factor ^ 2 :=
      lt_of_le_of_ne
        (Order.Arithmetic.sq_nonneg_direct factor)
        factorSquareNonzero.symm
    rw [targetValue]
    exact Order.Arithmetic.mul_pos_direct factorSquarePositive
      (nonNullProportion_norm_positive proportion)
  · intro targetPositive
    let positiveTarget : PositiveSquareClassRepresentative :=
      ⟨target, targetPositive⟩
    have preimageValue := preimage_quadranceClass algorithm positiveTarget
    change (preimage algorithm positiveTarget).toProportion.norm =
      target.value at preimageValue
    refine ⟨preimage algorithm positiveTarget, 1, target.one_ne_zero, ?_⟩
    change target.value =
      (1 : Fraction.Rational) ^ 2 *
        (preimage algorithm positiveTarget).toProportion.norm
    rw [preimageValue]
    ring1

/-- The rational quadrance-class image consists exactly of positive representatives.

The retained finite Lagrange algorithm supplies the four-square preimages. -/
theorem
  quadranceClassImage_iff_positive
    (target : SquareClassRepresentative Fraction.Rational) :
    InQuadranceClassImage target ↔ 0 < target.value :=
  inQuadranceClassImage_iff_positive Rational.TheoremSixtyTwo.lagrangeAlgorithm target

end TheoremSixtyTwo

end Purelib.Algebra.Quaternion.Projective.Rational.Surjectivity

end
