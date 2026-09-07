import RationalRotations.FiniteGeneratedSubgroups
import RationalRotations.FiniteGeneratorProfileExamples

/-!
# Checked finite-query subgroup-classification examples

The regressions below use the rank-two rotation profile with a redundant
product generator and a repeated generator.  They distinguish equality of
rotations from equality modulo the unit-quaternion kernel.
-/

namespace RationalRotations

namespace FiniteGeneratedSubgroupExamples

open FiniteGeneratorProfileExamples

def classification := FiniteGeneratedSubgroups.classify
  [ExampleSixtyFour.quarterTurn.rotation,
    ExampleSixtyFour.threeFourFive.rotation,
    productRotation,
    ExampleSixtyFour.quarterTurn.rotation]

theorem classification_rank :
    classification.profile.targetProfile.span.rank = 2 := by
  decide +kernel

theorem classification_image_cardinality :
    classification.profile.targetProfile.span.entries.length = 4 := by
  decide +kernel

/-- The displayed forward--inverse pair is certified to lie in the kernel,
not merely to have a suggestive zero signature. -/
theorem inversePairWord_in_kernel :
    NonNullProportion.HasUnitRepresentative
      (FiniteRotationProfiles.signedWordProduct redundantRotationProfile
        inversePairWord) :=
  (FiniteGeneratedSubgroups.signedWord_hasUnitRepresentative_iff_vector_zero
      redundantRotationProfile inversePairWord).mpr inversePairWord_vector

/-- The same word is in the identity kernel coset. -/
theorem inversePairWord_same_identity_coset :
    NonNullProportion.InSameUnitKernelCoset
      (FiniteRotationProfiles.signedWordProduct redundantRotationProfile
        inversePairWord)
      (FiniteRotationProfiles.signedWordProduct redundantRotationProfile
        []) := by
  apply (FiniteGeneratedSubgroups.signedWords_sameKernelCoset_iff_vector_eq
    redundantRotationProfile inversePairWord []).mpr
  rw [inversePairWord_vector]
  rfl

/-- Forward and inverse quarter turns occupy the same `chi` coset. -/
theorem forward_inverse_same_kernel_coset :
    NonNullProportion.InSameUnitKernelCoset
      (FiniteRotationProfiles.signedWordProduct redundantRotationProfile
        [firstForward])
      (FiniteRotationProfiles.signedWordProduct redundantRotationProfile
        [firstInverse]) := by
  apply (FiniteGeneratedSubgroups.signedWords_sameKernelCoset_iff_vector_eq
    redundantRotationProfile [firstForward] [firstInverse]).mpr
  rfl

/-- They are nevertheless different rotations, so the finite quotient
classifier is not being confused with equality in the generated group. -/
theorem forward_inverse_different_rotations :
    (FiniteRotationProfiles.signedWordProduct redundantRotationProfile
        [firstForward]).rotationMatrix ≠
      (FiniteRotationProfiles.signedWordProduct redundantRotationProfile
        [firstInverse]).rotationMatrix := by
  decide +kernel

/-- The inverse-word algorithm returns the displayed inverse generator. -/
theorem firstForward_inverse_product :
    FiniteRotationProfiles.signedWordProduct redundantRotationProfile
        (FiniteGeneratedSubgroups.inverseWord [firstForward]) =
      NonNullProportion.conjugate
        (FiniteRotationProfiles.signedWordProduct redundantRotationProfile
          [firstForward]) :=
  FiniteGeneratedSubgroups.signedWordProduct_inverseWord
    redundantRotationProfile [firstForward]

/-- A queried kernel word retains an explicit normalizer whose scaled norm
is its computed square-free natural kernel. -/
theorem inversePairWord_normalization_spec :
    let evaluation := FiniteGeneratedSubgroups.evaluate
      redundantRotationProfile inversePairWord
    (Proportion.scale evaluation.normalization.factor
      evaluation.proportion.toProportion).norm =
        (evaluation.normalization.signature.kernel :
          FiniteRotationProfiles.Scalar) :=
  (FiniteGeneratedSubgroups.evaluate redundantRotationProfile
    inversePairWord).normalization.norm_eq_kernel

end FiniteGeneratedSubgroupExamples

end RationalRotations
