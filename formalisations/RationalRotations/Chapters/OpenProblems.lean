module
import Purelib.Geometry.Rotations.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction

public import Purelib.Geometry.Rotations.Cayley.CoefficientProducts
public import Purelib.Geometry.Rotations.Rational.Generators.Classification
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field

open Purelib.Algebra

open Purelib.Data.Rat

open Purelib.Geometry

section
@[expose] public section

/-!
# Section 13.3: open problems

Problem 68 is refuted as printed by the projection counterexample already
recorded for Conjecture 52; its hardened unital five-parameter replacement is
proved over the paper's primary rational field.  For Problem 69, the missing PDF glyph is the
quadrance-class homomorphism `chi`, represented here by
`RotationQuadranceClass.ofRotation`; the exact excluded affine quadric is
`Q = -1`.  The executable finite enumerators and small-field regression
tables live in `FiniteFieldCounting`.  Problems 70 and 71 retain the pointwise
finite data and algebraic parts that follow from the preceding development;
Problem 70's finitely generated subgroup clause is classified through exact
arbitrary finite-word queries and its complete finite `chi` quotient;
Problem 72 is completed by the constructive projective polarity in
`ProjectiveDuality`.
-/

namespace formalisations.RationalRotations.Chapters.OpenProblems

variable {K : Type*} [Field.ExplicitField K]

/-! ## Problem 68 -/

/-- Problem 68 repeats Conjecture 52 and is false without additional
nondegeneracy hypotheses. -/
theorem problemSixtyEight_false (twoNonzero : (2 : K) ≠ 0) :
    ¬ (@Rotations.Cayley.CoefficientProducts.CoefficientProductParameters.AssociativityConjecture K _) :=
  Rotations.Cayley.CoefficientProducts.CoefficientProductParameters.associativityConjecture_false twoNonzero

/-- Problem 68 is already false in the exact denominator-constant-one,
four-coefficient family printed in the paper. -/
theorem problemSixtyEight_normalized_false (twoNonzero : (2 : K) ≠ 0) :
    ¬ (@Rotations.Cayley.CoefficientProducts.NormalizedCoefficientProductParameters.AssociativityConjecture K _) :=
  Rotations.Cayley.CoefficientProducts.NormalizedCoefficientProductParameters.associativityConjecture_false
    twoNonzero

/-- Corrected Problem 68 over the rationals: a homogeneous five-parameter
coefficient product has zero as a two-sided identity and is associative on
every defined bracketing exactly when `α = β = ι ≠ 0` and `ιδ = -γ²`. -/
theorem problemSixtyEight_corrected
    (parameters : Rotations.Cayley.CoefficientProducts.CoefficientProductParameters
      Fraction.Rational) :
    (parameters.HasZeroIdentity ∧ parameters.AssociativeWhereDefined) ↔
      parameters.constantCoefficient ≠ 0 ∧
      parameters.leftCoefficient = parameters.constantCoefficient ∧
      parameters.rightCoefficient = parameters.constantCoefficient ∧
      parameters.constantCoefficient * parameters.dotCoefficient =
        -(parameters.crossCoefficient ^ 2) :=
  parameters.rational_hardenedAssociativityClassification

/-- The strongest finite-only form of Problem 70's finitely generated
subgroup classification.  It computes the exact finite `chi` quotient and
answers arbitrary signed-word evaluation, equality, kernel-membership, and
kernel-coset queries without constructing the generally infinite subgroup. -/
abbrev ProblemSeventyGeneratedClassification
    (rotations : List
      (Rotations.Basic.Rotation Fraction.Rational)) :=
  Purelib.Geometry.Rotations.Rational.Generators.Classification rotations

/-- Construct the finite square-class classifier for the supplied rational rotations.

Retain the exact finite image and the signed-word, equality, kernel-membership and kernel-coset query operations for
those original generators. -/
def problemSeventyGeneratedClassification
    (rotations : List
      (Rotations.Basic.Rotation Fraction.Rational)) :
    ProblemSeventyGeneratedClassification rotations :=
  Rotations.Rational.Generators.Classification.GeneratedSubgroups.classify rotations

end formalisations.RationalRotations.Chapters.OpenProblems

end
