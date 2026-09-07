import RationalRotations.FiniteGeneratorProfiles

/-!
# Finite chi profiles of supplied rational rotations

This module is the rotation-facing wrapper around the finite positive
square-class span.  Every input rotation is paired once with its canonical
projective proportion and its positive norm target.  The cached targets are
then passed to the finite Boolean profile; downstream code does not recompute
the inverse representative or its norm.
-/

namespace RationalRotations

namespace FiniteRotationProfiles

abbrev Scalar := RFAP.ConstructiveFraction.Rational

abbrev Target := FiniteGeneratorProfiles.Target

/-- Regard the norm of one displayed rational proportion as a positive
square-class target. -/
def proportionTarget (proportion : NonNullProportion Scalar) : Target where
  representative := proportion.quadranceClass
  positive := TheoremSixtyTwo.nonNullProportion_norm_positive proportion

private theorem target_eq_of_representative_eq {left right : Target}
    (equal : left.representative = right.representative) : left = right := by
  cases left with
  | mk leftRepresentative leftPositive =>
      cases right with
      | mk rightRepresentative rightPositive =>
          dsimp only at equal
          subst rightRepresentative
          rfl

theorem proportionTarget_mul (left right : NonNullProportion Scalar) :
    proportionTarget (NonNullProportion.mul left right) =
      PositiveSquareClassSignatures.mulTarget
        (proportionTarget left) (proportionTarget right) := by
  apply target_eq_of_representative_eq
  exact NonNullProportion.quadranceClass_mul left right

theorem proportionTarget_conjugate (proportion : NonNullProportion Scalar) :
    proportionTarget (NonNullProportion.conjugate proportion) =
      proportionTarget proportion := by
  apply target_eq_of_representative_eq
  apply SquareClassRepresentative.ext
  exact Proportion.norm_conjugate proportion.toProportion

/-- A fixed rational identity representative, used as the empty signed-word
product without requiring an inhabitant from the supplied generator list. -/
def identityProportion : NonNullProportion Scalar where
  scalar := 1
  vector := Vector.zero
  normNonzero := by
    unfold Proportion.norm
    rw [Vector.quadrance_zero]
    simpa only [one_pow, add_zero] using (by decide : (1 : Scalar) ≠ 0)

/-- The canonical finite signature of the displayed identity has no prime
support. -/
theorem identity_target_primes_empty :
    (PositiveSquareClassSignatures.compute
      (proportionTarget identityProportion)).primes = [] := by
  let signature := PositiveSquareClassSignatures.compute
    (proportionTarget identityProportion)
  have sourceOne : signature.source = 1 := by
    rw [signature.source_eq]
    rfl
  have productDividesOne : signature.primes.prod ∣ 1 := by
    refine ⟨signature.root ^ 2, ?_⟩
    calc
      1 = signature.source := sourceOne.symm
      _ = signature.root ^ 2 * signature.primes.prod :=
        signature.decomposition
      _ = signature.primes.prod * signature.root ^ 2 := Nat.mul_comm _ _
  cases supportEq : signature.primes with
  | nil => rfl
  | cons prime tail =>
      have primeMember : prime ∈ signature.primes := by
        rw [supportEq]
        exact List.mem_cons_self
      have primeDividesProduct : prime ∣ signature.primes.prod := by
        refine ⟨tail.prod, ?_⟩
        rw [supportEq, List.prod_cons]
      have primeDividesOne : prime ∣ 1 :=
        Nat.dvd_trans primeDividesProduct productDividesOne
      exact False.elim
        ((signature.primes_prime prime primeMember).not_dvd_one
          primeDividesOne)

theorem identity_signature_zero (finiteSupport : List Nat) :
    FiniteGeneratorProfiles.signatureVector finiteSupport
        (proportionTarget identityProportion) =
      RFAP.FiniteBooleanSpan.zero finiteSupport.length := by
  apply RFAP.FiniteBooleanSpan.Vector.ext
  change FiniteGeneratorProfiles.signatureBits finiteSupport
      (PositiveSquareClassSignatures.compute
        (proportionTarget identityProportion)).primes =
    List.replicate finiteSupport.length false
  rw [identity_target_primes_empty]
  induction finiteSupport with
  | nil => rfl
  | cons _prime tail inductionHypothesis =>
      simp only [FiniteGeneratorProfiles.signatureBits, List.map_cons,
        PositiveSquareClassSignatures.natContains, List.length_cons,
        List.replicate_succ, List.cons.injEq, true_and]
      exact inductionHypothesis

/-- One supplied rotation together with the canonical inverse representative
and positive square-class target used by the finite profile. -/
structure GeneratorEntry where
  rotation : Rotation Scalar
  proportion : NonNullProportion Scalar
  proportion_eq :
    proportion = RotationProportion.ofRotation rotation (by decide)
  proportion_represents : proportion.rotationMatrix = rotation.matrix
  target : Target
  target_eq : target = proportionTarget proportion

/-- Cache the canonical projective representative and norm target of one
supplied rational rotation. -/
def generatorEntry (rotation : Rotation Scalar) : GeneratorEntry := by
  let proportion := RotationProportion.ofRotation rotation (by decide)
  exact
    { rotation := rotation
      proportion := proportion
      proportion_eq := rfl
      proportion_represents :=
        RotationProportion.ofRotation_rotationMatrix rotation (by decide)
      target := proportionTarget proportion
      target_eq := rfl }

/-- Cache the canonical data for every member of one supplied finite rotation
list. -/
def generatorEntries (rotations : List (Rotation Scalar)) :
    List GeneratorEntry :=
  rotations.map generatorEntry

theorem generatorEntries_length (rotations : List (Rotation Scalar)) :
    (generatorEntries rotations).length = rotations.length := by
  rw [generatorEntries, List.length_map]

theorem generatorEntries_rotations (rotations : List (Rotation Scalar)) :
    (generatorEntries rotations).map GeneratorEntry.rotation = rotations := by
  induction rotations with
  | nil => rfl
  | cons rotation tail inductionHypothesis =>
      simp only [generatorEntries, List.map_cons, generatorEntry]
      exact congrArg (List.cons rotation) inductionHypothesis

/-- The complete finite part of a supplied rational generator system visible
through the quadrance-class map. -/
structure VisibleRotationProfile (rotations : List (Rotation Scalar)) where
  generators : List GeneratorEntry
  generators_eq : generators = generatorEntries rotations
  generators_length : generators.length = rotations.length
  generators_rotations : generators.map GeneratorEntry.rotation = rotations
  targetProfile : FiniteGeneratorProfiles.VisibleGeneratorProfile
    (generators.map GeneratorEntry.target)

/-- Compute the finite chi-visible profile of one supplied rational rotation
list, retaining every canonical inverse representative used to obtain it. -/
def visibleRotationProfile (rotations : List (Rotation Scalar)) :
    VisibleRotationProfile rotations := by
  let generators := generatorEntries rotations
  exact
    { generators := generators
      generators_eq := rfl
      generators_length := generatorEntries_length rotations
      generators_rotations := generatorEntries_rotations rotations
      targetProfile := FiniteGeneratorProfiles.visibleGeneratorProfile
        (generators.map GeneratorEntry.target) }

theorem visibleRotationProfile_image_length
    (rotations : List (Rotation Scalar)) :
    (visibleRotationProfile rotations).targetProfile.span.entries.length =
      2 ^ (visibleRotationProfile rotations).targetProfile.span.rank :=
  (visibleRotationProfile rotations).targetProfile.span.length_eq

theorem visibleRotationProfile_image_nodup
    (rotations : List (Rotation Scalar)) :
    (((visibleRotationProfile rotations).targetProfile.span.entries.map
      RFAP.FiniteBooleanSpan.Entry.vector)).Nodup :=
  (visibleRotationProfile rotations).targetProfile.span.vectors_nodup

/-- One occurrence in an arbitrary finite signed word over a supplied
rotation profile.  Membership is retained as a certificate; `inverse = true`
selects quaternion conjugation. -/
structure SignedLetter {rotations : List (Rotation Scalar)}
    (profile : VisibleRotationProfile rotations) where
  generator : GeneratorEntry
  member : generator ∈ profile.generators
  inverse : Bool

/-- Select one cached canonical proportion with a displayed sign. -/
def signedGeneratorProportion (generator : GeneratorEntry) (inverse : Bool) :
    NonNullProportion Scalar :=
  match inverse with
  | false => generator.proportion
  | true => NonNullProportion.conjugate generator.proportion

/-- Select the cached canonical proportion or its explicit conjugate. -/
def selectedProportion {rotations : List (Rotation Scalar)}
    {profile : VisibleRotationProfile rotations}
    (letter : SignedLetter profile) : NonNullProportion Scalar :=
  signedGeneratorProportion letter.generator letter.inverse

/-- Evaluate one arbitrary supplied finite signed word as a quaternion
product. -/
def signedWordProduct {rotations : List (Rotation Scalar)}
    (profile : VisibleRotationProfile rotations) :
    List (SignedLetter profile) → NonNullProportion Scalar
  | [] => identityProportion
  | letter :: tail =>
      NonNullProportion.mul (selectedProportion letter)
        (signedWordProduct profile tail)

/-- Multiply the positive targets of the word.  Inversion disappears here
because a quaternion and its conjugate have equal norm class. -/
def signedWordTarget {rotations : List (Rotation Scalar)}
    (profile : VisibleRotationProfile rotations) :
    List (SignedLetter profile) → Target
  | [] => proportionTarget identityProportion
  | letter :: tail =>
      PositiveSquareClassSignatures.mulTarget letter.generator.target
        (signedWordTarget profile tail)

theorem selectedProportion_target
    {rotations : List (Rotation Scalar)}
    {profile : VisibleRotationProfile rotations}
    (letter : SignedLetter profile) :
    proportionTarget (selectedProportion letter) = letter.generator.target := by
  cases inverseEq : letter.inverse with
  | false =>
      simpa only [selectedProportion, signedGeneratorProportion, inverseEq]
        using
        letter.generator.target_eq.symm
  | true =>
      simpa only [selectedProportion, signedGeneratorProportion, inverseEq]
        using
        (proportionTarget_conjugate letter.generator.proportion).trans
          letter.generator.target_eq.symm

theorem signedWordProduct_target
    {rotations : List (Rotation Scalar)}
    (profile : VisibleRotationProfile rotations) :
    ∀ word : List (SignedLetter profile),
      proportionTarget (signedWordProduct profile word) =
        signedWordTarget profile word
  | [] => rfl
  | letter :: tail => by
      change proportionTarget
          (NonNullProportion.mul (selectedProportion letter)
            (signedWordProduct profile tail)) =
        PositiveSquareClassSignatures.mulTarget letter.generator.target
          (signedWordTarget profile tail)
      rw [proportionTarget_mul, selectedProportion_target,
        signedWordProduct_target profile tail]

/-- Signature vectors of the occurrences in a supplied signed word.  The sign
does not alter a norm square class. -/
def signedWordVectors {rotations : List (Rotation Scalar)}
    (profile : VisibleRotationProfile rotations)
    (word : List (SignedLetter profile)) :
    List (RFAP.FiniteBooleanSpan.Vector
      profile.targetProfile.finiteSupport.length) :=
  word.map fun letter =>
    FiniteGeneratorProfiles.signatureVector
      profile.targetProfile.finiteSupport letter.generator.target

/-- XOR evaluation of the finite signed word on the displayed shared prime
support. -/
def signedWordVector {rotations : List (Rotation Scalar)}
    (profile : VisibleRotationProfile rotations)
    (word : List (SignedLetter profile)) :
    RFAP.FiniteBooleanSpan.Vector
      profile.targetProfile.finiteSupport.length :=
  (signedWordVectors profile word).foldr RFAP.FiniteBooleanSpan.xor
    (RFAP.FiniteBooleanSpan.zero profile.targetProfile.finiteSupport.length)

theorem signedWordVectors_mem
    {rotations : List (Rotation Scalar)}
    (profile : VisibleRotationProfile rotations)
    (word : List (SignedLetter profile)) :
    ∀ vector ∈ signedWordVectors profile word,
      vector ∈ profile.targetProfile.vectors := by
  intro vector vectorMember
  rcases QuotientFreeList.mem_map.mp vectorMember with
    ⟨letter, letterMember, vectorEq⟩
  rw [profile.targetProfile.vectors_eq]
  apply QuotientFreeList.mem_map.mpr
  refine ⟨letter.generator.target, ?_, vectorEq⟩
  apply QuotientFreeList.mem_map.mpr
  exact ⟨letter.generator, letter.member, rfl⟩

theorem signedWordTarget_signature
    {rotations : List (Rotation Scalar)}
    (profile : VisibleRotationProfile rotations) :
    ∀ word : List (SignedLetter profile),
      FiniteGeneratorProfiles.signatureVector
          profile.targetProfile.finiteSupport
          (signedWordTarget profile word) =
        signedWordVector profile word
  | [] => identity_signature_zero profile.targetProfile.finiteSupport
  | letter :: tail => by
      change FiniteGeneratorProfiles.signatureVector
          profile.targetProfile.finiteSupport
          (PositiveSquareClassSignatures.mulTarget letter.generator.target
            (signedWordTarget profile tail)) =
        RFAP.FiniteBooleanSpan.xor
          (FiniteGeneratorProfiles.signatureVector
            profile.targetProfile.finiteSupport letter.generator.target)
          (signedWordVector profile tail)
      rw [FiniteGeneratorProfiles.signatureVector_mul,
        signedWordTarget_signature profile tail]

/-- Folding an arbitrary supplied finite signed rotation word and folding its
finite prime-parity signatures commute with the quadrance-class map. -/
theorem signedWordProduct_signature
    {rotations : List (Rotation Scalar)}
    (profile : VisibleRotationProfile rotations)
    (word : List (SignedLetter profile)) :
    FiniteGeneratorProfiles.signatureVector
        profile.targetProfile.finiteSupport
        (proportionTarget (signedWordProduct profile word)) =
      signedWordVector profile word := by
  rw [signedWordProduct_target profile word]
  exact signedWordTarget_signature profile word

/-- Every arbitrary supplied finite signed word is classified by one retained
entry of the exact finite chi-image. -/
theorem classifySignedWord
    {rotations : List (Rotation Scalar)}
    (profile : VisibleRotationProfile rotations)
    (word : List (SignedLetter profile)) :
    ∃ entry ∈ profile.targetProfile.span.entries,
      signedWordVector profile word = entry.vector :=
  profile.targetProfile.span.classifyXorWord
    (signedWordVectors profile word)
    (signedWordVectors_mem profile word)

/-- A compact signed word aligned with the supplied generator list.  A false
choice omits that generator; a true choice uses it once in the displayed
direction.  This finite normal form is sufficient for every element of the
Boolean chi-image. -/
structure SignedSelectionWord {rotations : List (Rotation Scalar)}
    (profile : VisibleRotationProfile rotations) where
  choices : List Bool
  choices_length : choices.length = profile.generators.length
  inverses : List Bool
  inverses_length : inverses.length = profile.generators.length

private def selectionProductFrom :
    List GeneratorEntry → List Bool → List Bool → NonNullProportion Scalar
  | generator :: generators, true :: choices, inverse :: inverses =>
      NonNullProportion.mul
        (signedGeneratorProportion generator inverse)
        (selectionProductFrom generators choices inverses)
  | _generator :: generators, false :: choices, _inverse :: inverses =>
      selectionProductFrom generators choices inverses
  | _, _, _ => identityProportion

/-- Evaluate the compact signed selection as an explicit finite quaternion
product. -/
def signedSelectionProduct {rotations : List (Rotation Scalar)}
    (profile : VisibleRotationProfile rotations)
    (word : SignedSelectionWord profile) : NonNullProportion Scalar :=
  selectionProductFrom profile.generators word.choices word.inverses

private theorem signedGeneratorProportion_target
    (generator : GeneratorEntry) (inverse : Bool) :
    proportionTarget (signedGeneratorProportion generator inverse) =
      generator.target := by
  cases inverse with
  | false => exact generator.target_eq.symm
  | true =>
      exact (proportionTarget_conjugate generator.proportion).trans
        generator.target_eq.symm

private theorem selectionProductFrom_signature (finiteSupport : List Nat) :
    ∀ (generators : List GeneratorEntry)
      (choices inverses : List Bool),
      choices.length = generators.length →
      inverses.length = generators.length →
      FiniteGeneratorProfiles.signatureVector finiteSupport
          (proportionTarget
            (selectionProductFrom generators choices inverses)) =
        RFAP.FiniteBooleanSpan.evaluate choices
          (generators.map fun generator =>
            FiniteGeneratorProfiles.signatureVector finiteSupport
              generator.target)
  | [], choices, inverses, choicesLength, inversesLength => by
      cases choices with
      | cons _head _tail => nomatch choicesLength
      | nil =>
          cases inverses with
          | cons _head _tail => nomatch inversesLength
          | nil => exact identity_signature_zero finiteSupport
  | generator :: generators, choices, inverses, choicesLength,
      inversesLength => by
      cases choices with
      | nil => nomatch choicesLength
      | cons choice tailChoices =>
          cases inverses with
          | nil => nomatch inversesLength
          | cons inverse tailInverses =>
              have tailChoicesLength :
                  tailChoices.length = generators.length :=
                Nat.succ.inj choicesLength
              have tailInversesLength :
                  tailInverses.length = generators.length :=
                Nat.succ.inj inversesLength
              cases choice with
              | false =>
                  exact selectionProductFrom_signature finiteSupport
                    generators tailChoices tailInverses tailChoicesLength
                    tailInversesLength
              | true =>
                  change FiniteGeneratorProfiles.signatureVector finiteSupport
                      (proportionTarget
                        (NonNullProportion.mul
                          (signedGeneratorProportion generator inverse)
                          (selectionProductFrom generators tailChoices
                            tailInverses))) =
                    RFAP.FiniteBooleanSpan.xor
                      (FiniteGeneratorProfiles.signatureVector finiteSupport
                        generator.target)
                      (RFAP.FiniteBooleanSpan.evaluate tailChoices
                        (generators.map fun tailGenerator =>
                          FiniteGeneratorProfiles.signatureVector finiteSupport
                            tailGenerator.target))
                  rw [proportionTarget_mul,
                    signedGeneratorProportion_target,
                    FiniteGeneratorProfiles.signatureVector_mul,
                    selectionProductFrom_signature finiteSupport generators
                      tailChoices tailInverses tailChoicesLength
                      tailInversesLength]

private theorem map_target_vectors (finiteSupport : List Nat) :
    ∀ generators : List GeneratorEntry,
      (generators.map GeneratorEntry.target).map
          (FiniteGeneratorProfiles.signatureVector finiteSupport) =
        generators.map fun generator =>
          FiniteGeneratorProfiles.signatureVector finiteSupport
            generator.target
  | [] => rfl
  | _generator :: generators => by
      simp only [List.map_cons, List.cons.injEq, true_and]
      exact map_target_vectors finiteSupport generators

/-- The compact signed-word product has exactly the Boolean signature obtained
by evaluating its choices against the cached generator vectors. -/
theorem signedSelectionProduct_signature
    {rotations : List (Rotation Scalar)}
    (profile : VisibleRotationProfile rotations)
    (word : SignedSelectionWord profile) :
    FiniteGeneratorProfiles.signatureVector
        profile.targetProfile.finiteSupport
        (proportionTarget (signedSelectionProduct profile word)) =
      RFAP.FiniteBooleanSpan.evaluate word.choices
        profile.targetProfile.vectors := by
  rw [profile.targetProfile.vectors_eq]
  have mappedVectors :
      (profile.generators.map GeneratorEntry.target).map
          (FiniteGeneratorProfiles.signatureVector
            profile.targetProfile.finiteSupport) =
        profile.generators.map fun generator =>
          FiniteGeneratorProfiles.signatureVector
            profile.targetProfile.finiteSupport generator.target :=
    map_target_vectors profile.targetProfile.finiteSupport profile.generators
  rw [mappedVectors]
  unfold signedSelectionProduct
  exact selectionProductFrom_signature profile.targetProfile.finiteSupport
    profile.generators word.choices word.inverses word.choices_length
    word.inverses_length

/-- Turn the Boolean choices retained by an image entry into an explicit
forward-only signed generator word. -/
def entrySignedWord
    {rotations : List (Rotation Scalar)}
    (profile : VisibleRotationProfile rotations)
    (entry : RFAP.FiniteBooleanSpan.Entry
      profile.targetProfile.vectors) : SignedSelectionWord profile := by
  have vectorsLength : profile.targetProfile.vectors.length =
      profile.generators.length := by
    rw [profile.targetProfile.vectors_eq, List.length_map, List.length_map]
  exact
    { choices := entry.choices
      choices_length := entry.choices_length.trans vectorsLength
      inverses := List.replicate profile.generators.length false
      inverses_length := List.length_replicate }

/-- Every listed finite-image signature retains a signed generator word whose
explicit quaternion product realizes that signature. -/
theorem entrySignedWord_realizes
    {rotations : List (Rotation Scalar)}
    (profile : VisibleRotationProfile rotations)
    (entry : RFAP.FiniteBooleanSpan.Entry
      profile.targetProfile.vectors) :
    FiniteGeneratorProfiles.signatureVector
        profile.targetProfile.finiteSupport
        (proportionTarget
          (signedSelectionProduct profile (entrySignedWord profile entry))) =
      entry.vector := by
  rw [signedSelectionProduct_signature]
  exact entry.evaluates

end FiniteRotationProfiles

end RationalRotations
