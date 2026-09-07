import RationalRotations.FiniteRotationProfiles
import RationalRotations.QuaternionObstruction

/-!
# Checked finite chi-profile examples

These examples exercise the exact finite Boolean image on a trivial system,
one independent square class, and a rank-two system with redundant classes.
-/

namespace RationalRotations

namespace FiniteGeneratorProfileExamples

open PositiveSquareClassSignatures

def one : FiniteGeneratorProfiles.Target :=
  positiveNaturalTarget 1 (by decide)

def two : FiniteGeneratorProfiles.Target :=
  positiveNaturalTarget 2 (by decide)

def three : FiniteGeneratorProfiles.Target :=
  positiveNaturalTarget 3 (by decide)

def six : FiniteGeneratorProfiles.Target :=
  positiveNaturalTarget 6 (by decide)

def trivialProfile :=
  FiniteGeneratorProfiles.visibleGeneratorProfile [one]

def rankOneProfile :=
  FiniteGeneratorProfiles.visibleGeneratorProfile [two, two]

def redundantRankTwoProfile :=
  FiniteGeneratorProfiles.visibleGeneratorProfile [two, three, six, two]

theorem trivialProfile_rank : trivialProfile.span.rank = 0 := by
  decide +kernel

theorem trivialProfile_image_length : trivialProfile.span.entries.length = 1 :=
  by decide +kernel

theorem rankOneProfile_rank : rankOneProfile.span.rank = 1 := by
  decide +kernel

theorem rankOneProfile_image_length :
    rankOneProfile.span.entries.length = 2 := by decide +kernel

theorem redundantRankTwoProfile_rank :
    redundantRankTwoProfile.span.rank = 2 := by decide +kernel

theorem redundantRankTwoProfile_image_length :
    redundantRankTwoProfile.span.entries.length = 4 := by decide +kernel

/-- The same rank-two pattern at the rotation-facing boundary: norms `2` and
`5`, their product, and a repeated first generator. -/
def productRotation : Rotation FiniteRotationProfiles.Scalar :=
  (NonNullProportion.mul ExampleSixtyFour.quarterTurn
    ExampleSixtyFour.threeFourFive).rotation

def redundantRotationProfile :=
  FiniteRotationProfiles.visibleRotationProfile
    [ExampleSixtyFour.quarterTurn.rotation,
      ExampleSixtyFour.threeFourFive.rotation,
      productRotation,
      ExampleSixtyFour.quarterTurn.rotation]

theorem redundantRotationProfile_generators_length :
    redundantRotationProfile.generators.length = 4 := by decide +kernel

theorem redundantRotationProfile_rank :
    redundantRotationProfile.targetProfile.span.rank = 2 := by
  decide +kernel

theorem redundantRotationProfile_image_length :
    redundantRotationProfile.targetProfile.span.entries.length = 4 := by
  decide +kernel

def firstForward :
    FiniteRotationProfiles.SignedLetter redundantRotationProfile where
  generator := FiniteRotationProfiles.generatorEntry
    ExampleSixtyFour.quarterTurn.rotation
  member := by
    change FiniteRotationProfiles.generatorEntry
      ExampleSixtyFour.quarterTurn.rotation ∈
        FiniteRotationProfiles.generatorEntries
          [ExampleSixtyFour.quarterTurn.rotation,
            ExampleSixtyFour.threeFourFive.rotation,
            productRotation,
            ExampleSixtyFour.quarterTurn.rotation]
    exact List.mem_cons_self
  inverse := false

def firstInverse :
    FiniteRotationProfiles.SignedLetter redundantRotationProfile where
  generator := FiniteRotationProfiles.generatorEntry
    ExampleSixtyFour.quarterTurn.rotation
  member := firstForward.member
  inverse := true

def inversePairWord := [firstForward, firstInverse]

theorem inversePairWord_vector :
    FiniteRotationProfiles.signedWordVector redundantRotationProfile
        inversePairWord =
      RFAP.FiniteBooleanSpan.zero
        redundantRotationProfile.targetProfile.finiteSupport.length := by
  unfold FiniteRotationProfiles.signedWordVector
    FiniteRotationProfiles.signedWordVectors inversePairWord
  simp only [List.map_cons, List.map_nil, List.foldr]
  rw [RFAP.FiniteBooleanSpan.xor_zero]
  change RFAP.FiniteBooleanSpan.xor
      (FiniteGeneratorProfiles.signatureVector
        redundantRotationProfile.targetProfile.finiteSupport
        (FiniteRotationProfiles.generatorEntry
          ExampleSixtyFour.quarterTurn.rotation).target)
      (FiniteGeneratorProfiles.signatureVector
        redundantRotationProfile.targetProfile.finiteSupport
        (FiniteRotationProfiles.generatorEntry
          ExampleSixtyFour.quarterTurn.rotation).target) =
    RFAP.FiniteBooleanSpan.zero
      redundantRotationProfile.targetProfile.finiteSupport.length
  exact RFAP.FiniteBooleanSpan.xor_self _

theorem inversePairWord_product_signature :
    FiniteGeneratorProfiles.signatureVector
        redundantRotationProfile.targetProfile.finiteSupport
        (FiniteRotationProfiles.proportionTarget
          (FiniteRotationProfiles.signedWordProduct redundantRotationProfile
            inversePairWord)) =
      RFAP.FiniteBooleanSpan.zero
        redundantRotationProfile.targetProfile.finiteSupport.length := by
  rw [FiniteRotationProfiles.signedWordProduct_signature,
    inversePairWord_vector]

theorem inversePairWord_classified :
    ∃ entry ∈ redundantRotationProfile.targetProfile.span.entries,
      FiniteRotationProfiles.signedWordVector redundantRotationProfile
          inversePairWord = entry.vector :=
  FiniteRotationProfiles.classifySignedWord redundantRotationProfile
    inversePairWord

end FiniteGeneratorProfileExamples

end RationalRotations
