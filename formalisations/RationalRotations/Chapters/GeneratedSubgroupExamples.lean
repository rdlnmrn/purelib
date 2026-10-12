module
import Purelib.Geometry.Rotations.Projective.Action
import Purelib.Algebra.Quaternion.Projective.UnitObstruction

import Purelib.Algebra.Quaternion.Projective.Basic
import Purelib.Geometry.Rotations.Rational.Generators.Profile
public import Purelib.Geometry.Rotations.Rational.Generators.Classification
public import formalisations.RationalRotations.Chapters.GeneratorProfileExamples
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Field
import Purelib.Examples.Geometry.Rotations.QuaternionObstruction
import Purelib.Geometry.Rotations.Basic
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.LinearAlgebra.Span.Boolean.Basic
import Purelib.NumberTheory.SquareClass.Rational.Signature
import Purelib.NumberTheory.SquareClass.Rational.Span

open Purelib

@[expose] public section

/-!
# Checked finite-query subgroup-classification examples

The regressions below use the rank-two rotation profile with a redundant
product generator and a repeated generator.  They distinguish equality of
rotations from equality modulo the unit-quaternion kernel.
-/

namespace formalisations.RationalRotations.Chapters

open Purelib.Geometry.Rotations.Rational.Generators.Classification

namespace GeneratedSubgroupExamples

open GeneratorProfileExamples

/-- The finite signed-word classifier for the quarter-turn, three-four-five rotation, their product and the repeated
quarter-turn.

It retains the rank-two square-class image together with exact word and kernel-query operations. -/
def classification := Geometry.Rotations.Rational.Generators.Classification.GeneratedSubgroups.classify
  [(Geometry.Rotations.Projective.Action.NonNullProportion.rotation
    Examples.Geometry.Rotations.QuaternionObstruction.ExampleSixtyFour.quarterTurn),
    (Geometry.Rotations.Projective.Action.NonNullProportion.rotation
      Examples.Geometry.Rotations.QuaternionObstruction.ExampleSixtyFour.threeFourFive),
    productRotation,
    (Geometry.Rotations.Projective.Action.NonNullProportion.rotation
      Examples.Geometry.Rotations.QuaternionObstruction.ExampleSixtyFour.quarterTurn)]

/-- The displayed generated subgroup profile has square-class rank two. -/
theorem classification_rank :
    classification.profile.targetProfile.span.rank = 2 := by
  decide +kernel

/-- The displayed generated subgroup profile has four entries in its finite square-class image. -/
theorem classification_image_cardinality :
    classification.profile.targetProfile.span.entries.length = 4 := by
  decide +kernel

/-- The displayed forward--inverse pair is certified to lie in the kernel,
not merely to have a suggestive zero signature. -/
theorem inversePairWord_in_kernel :
    Algebra.Quaternion.Projective.UnitObstruction.NonNullProportion.QuaternionObstruction.HasUnitRepresentative
      (Geometry.Rotations.Rational.Generators.Profile.RotationProfiles.signedWordProduct redundantRotationProfile
        inversePairWord) :=

    (GeneratedSubgroups.signedWord_hasUnitRepresentative_iff_vector_zero
      redundantRotationProfile inversePairWord).mpr inversePairWord_vector

/-- The same word is in the identity kernel coset. -/
theorem inversePairWord_same_identity_coset :
    Algebra.Quaternion.Projective.UnitObstruction.NonNullProportion.InSameUnitKernelCoset
      (Geometry.Rotations.Rational.Generators.Profile.RotationProfiles.signedWordProduct redundantRotationProfile
        inversePairWord)
      (Geometry.Rotations.Rational.Generators.Profile.RotationProfiles.signedWordProduct redundantRotationProfile
        []) := by
  apply
    (Geometry.Rotations.Rational.Generators.Classification.GeneratedSubgroups.signedWords_sameKernelCoset_iff_vector_eq
    redundantRotationProfile inversePairWord []).mpr
  rw [inversePairWord_vector]
  rfl

/-- Forward and inverse quarter turns occupy the same `chi` coset. -/
theorem forward_inverse_same_kernel_coset :
    Algebra.Quaternion.Projective.UnitObstruction.NonNullProportion.InSameUnitKernelCoset
      (Geometry.Rotations.Rational.Generators.Profile.RotationProfiles.signedWordProduct redundantRotationProfile
        [firstForward])
      (Geometry.Rotations.Rational.Generators.Profile.RotationProfiles.signedWordProduct redundantRotationProfile
        [firstInverse]) := by
  apply
    (Geometry.Rotations.Rational.Generators.Classification.GeneratedSubgroups.signedWords_sameKernelCoset_iff_vector_eq
    redundantRotationProfile [firstForward] [firstInverse]).mpr
  rfl

/-- They are nevertheless different rotations, so the finite quotient
classifier is not being confused with equality in the generated group. -/
theorem forward_inverse_different_rotations :
    (Geometry.Rotations.Projective.Action.NonNullProportion.rotationMatrix
      (Geometry.Rotations.Rational.Generators.Profile.RotationProfiles.signedWordProduct redundantRotationProfile
        [firstForward])) ≠
      (Geometry.Rotations.Projective.Action.NonNullProportion.rotationMatrix
        (Geometry.Rotations.Rational.Generators.Profile.RotationProfiles.signedWordProduct redundantRotationProfile
        [firstInverse])) := by
  decide +kernel

/-- The inverse-word algorithm returns the displayed inverse generator. -/
theorem firstForward_inverse_product :
    Geometry.Rotations.Rational.Generators.Profile.RotationProfiles.signedWordProduct redundantRotationProfile
        (Geometry.Rotations.Rational.Generators.Classification.GeneratedSubgroups.inverseWord [firstForward]) =
      Algebra.Quaternion.Projective.Basic.NonNullProportion.conjugate
        (Geometry.Rotations.Rational.Generators.Profile.RotationProfiles.signedWordProduct redundantRotationProfile
          [firstForward]) :=
  Geometry.Rotations.Rational.Generators.Classification.GeneratedSubgroups.signedWordProduct_inverseWord
    redundantRotationProfile [firstForward]

/-- A queried kernel word retains an explicit normalizer whose scaled norm
is its computed square-free natural kernel. -/
theorem inversePairWord_normalization_spec :
    let evaluation := Geometry.Rotations.Rational.Generators.Classification.GeneratedSubgroups.evaluate
      redundantRotationProfile inversePairWord
    (Algebra.Quaternion.Projective.Basic.Proportion.scale evaluation.normalization.factor
      evaluation.proportion.toProportion).norm =
        (evaluation.normalization.signature.kernel :
          Geometry.Rotations.Rational.Generators.Profile.RotationProfiles.Scalar) :=
  (Geometry.Rotations.Rational.Generators.Classification.GeneratedSubgroups.evaluate redundantRotationProfile
    inversePairWord).normalization.norm_eq_kernel

end GeneratedSubgroupExamples

end formalisations.RationalRotations.Chapters
