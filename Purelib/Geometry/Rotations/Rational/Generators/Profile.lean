module
import Purelib.Algebra.Field.SquareClass.Basic
public import Purelib.Algebra.Quaternion.Projective.Rational.Surjectivity
import Purelib.Algebra.Quaternion.Projective.SquareClass
import Purelib.Data.List.Map
import Purelib.Data.List.Replicate
import Purelib.Data.Nat.Divisibility
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Boolean.Basic
import Purelib.LinearAlgebra.Span.Boolean.Basic

import Purelib.Algebra.Quaternion.Projective.Basic
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Geometry.Rotations.Projective.Correspondence
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.NumberTheory.SquareClass.Rational.Signature
public import Purelib.NumberTheory.SquareClass.Rational.Span

import Purelib.Geometry.Rotations.Basic
import Init.Data.List.Basic
import Init.Data.List.Lemmas
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rotations.Projective.Action
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.NumberTheory.SquareClass.Rational.Basic

open Purelib

open Purelib.Algebra.Field.SquareClass.Basic

open Purelib.Algebra.Quaternion

open Purelib.Algebra.Quaternion.Projective.Basic

open Purelib.Algebra.Quaternion.Projective.Rational.Surjectivity

open Purelib.Algebra.Quaternion.Projective.SquareClass

open Purelib.Data.List
open Purelib.Data.Nat

open Purelib.Data.Rat

open Purelib.Data.Vector

open Purelib.Geometry

open Purelib.Geometry.Rotations.Projective.Action

open Purelib.Geometry.Rotations.Projective.Correspondence

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Span

open Purelib.LinearAlgebra.Span.Boolean.Basic

open Purelib.NumberTheory.SquareClass.Rational.Signature
open Purelib.NumberTheory.SquareClass.Rational.Basic

open Purelib.NumberTheory.SquareClass.Rational.Span

public section

/-!
# Finite chi profiles of supplied rational rotations

The supplied rotations retain their finite positive square-class span.  Every input rotation is paired once with its
canonical
projective proportion and its positive norm target.  The cached targets are
then passed to the finite Boolean profile; downstream code does not recompute
the inverse representative or its norm.
-/

namespace Purelib.Geometry.Rotations.Rational.Generators.Profile.RotationProfiles

open Purelib.Geometry.Rotations.Basic

open Purelib.LinearAlgebra.Coordinates3

section

/-- The constructive rational coefficient field of the retained rotation profiles. -/
abbrev Scalar := Fraction.Rational

/-- A positive square-class target for a generator norm. -/
abbrev Target := GeneratorProfiles.Target

/-- Regard the norm of one displayed rational proportion as a positive square-class target. -/
@[expose] def proportionTarget (proportion : Projective.Basic.NonNullProportion Scalar) :
  Target where
  representative := (NonNullProportion.quadranceClass proportion)
  positive := TheoremSixtyTwo.nonNullProportion_norm_positive proportion

/-- Quaternion multiplication multiplies the associated positive norm targets. -/
theorem proportionTarget_mul (left right : Projective.Basic.NonNullProportion Scalar) :
    proportionTarget (NonNullProportion.mul left right) =
      PositiveSquareClassSignatures.mulTarget
        (proportionTarget left) (proportionTarget right) := by
  apply (TheoremSixtyTwo.PositiveSquareClassRepresentative.mk.injEq _ _ _ _).mpr
  exact NonNullProportion.quadranceClass_mul left right

/-- Quaternion conjugation leaves the positive norm target unchanged. -/
theorem proportionTarget_conjugate (proportion : Projective.Basic.NonNullProportion Scalar) :
    proportionTarget (NonNullProportion.conjugate proportion) =
      proportionTarget proportion := by
  apply (TheoremSixtyTwo.PositiveSquareClassRepresentative.mk.injEq _ _ _ _).mpr
  apply SquareClassRepresentative.ext
  exact Proportion.norm_conjugate proportion.toProportion

/-- A fixed rational identity representative, used as the empty signed-word product without requiring an inhabitant from
the supplied generator list. -/
@[expose] def identityProportion : Projective.Basic.NonNullProportion Scalar where
  scalar := 1
  vector := Coordinates3.Vector.zero
  normNonzero := by
    unfold Projective.Basic.Proportion.norm
    rw [Coordinates3.Vector.quadrance_zero]
    simpa only [one_pow, add_zero] using (by decide : (1 : Scalar) ≠ 0)

/-- The canonical finite signature of the displayed identity has no prime support. -/
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
        Divisibility.trans primeDividesProduct productDividesOne
      exact False.elim
        ((signature.primes_prime prime primeMember).not_dvd_one
          primeDividesOne)

/-- The identity quaternion has the zero parity signature on every finite prime support. -/
theorem identity_signature_zero (finiteSupport : List Nat) :
    GeneratorProfiles.signatureVector finiteSupport
        (proportionTarget identityProportion) =
      Boolean.Basic.zero finiteSupport.length := by
  apply Data.Vector.Boolean.ext
  change GeneratorProfiles.signatureBits finiteSupport
      (PositiveSquareClassSignatures.compute
        (proportionTarget identityProportion)).primes =
    List.replicate finiteSupport.length false
  rw [identity_target_primes_empty]
  induction finiteSupport with
  | nil => rfl
  | cons _prime tail inductionHypothesis =>
      change false :: GeneratorProfiles.signatureBits tail [] =
        false :: List.replicate tail.length false
      exact congrArg (List.cons false) inductionHypothesis

set_option genInjectivity false in
/-- One supplied rotation together with the canonical inverse representative and positive square-class target used by
the finite profile. -/
structure GeneratorEntry where
  /-- The original supplied rational rotation. -/ rotation : Rotations.Basic.Rotation Scalar
  /-- The retained canonical non-null quaternion representative. -/ proportion : Projective.Basic.NonNullProportion
    Scalar
  /-- The cached proportion is exactly the canonical inverse representative of the supplied rotation. -/ proportion_eq :
    proportion = RotationProportion.ofRotation rotation (by decide)
  /-- The cached proportion has the original rotation matrix. -/ proportion_represents :
    (NonNullProportion.rotationMatrix proportion) = rotation.matrix
  /-- The cached positive norm target of the generator. -/ target : Target
  /-- The cached target is exactly the norm target of the cached proportion. -/ target_eq : target =
    proportionTarget proportion

constructive_injectivity GeneratorEntry

/-- Cache the canonical projective representative and norm target of one supplied rational rotation. -/
@[expose] def generatorEntry (rotation : Rotations.Basic.Rotation Scalar) : GeneratorEntry := by
  let proportion := RotationProportion.ofRotation rotation (by decide)
  exact
    { rotation := rotation
      proportion := proportion
      proportion_eq := rfl
      proportion_represents :=
        RotationProportion.ofRotation_rotationMatrix rotation (by decide)
      target := proportionTarget proportion
      target_eq := rfl }

/-- Cache the canonical data for every member of one supplied finite rotation list. -/
@[expose] def generatorEntries (rotations : List (Rotations.Basic.Rotation Scalar)) :
    List GeneratorEntry :=
  rotations.map generatorEntry

/-- Caching representatives preserves the length of the supplied rotation list. -/
theorem generatorEntries_length (rotations : List (Rotations.Basic.Rotation Scalar)) :
    (generatorEntries rotations).length = rotations.length := by
  rw [generatorEntries, Map.length_map]

/-- Reading the rotations from the cached entries recovers the original ordered list. -/
theorem generatorEntries_rotations (rotations : List (Rotations.Basic.Rotation Scalar)) :
    (generatorEntries rotations).map RotationProfiles.GeneratorEntry.rotation = rotations := by
  induction rotations with
  | nil => rfl
  | cons rotation tail inductionHypothesis =>
      simp only [generatorEntries, List.map_cons, generatorEntry]
      exact congrArg (List.cons rotation) inductionHypothesis

set_option genInjectivity false in
/-- The complete finite part of a supplied rational generator system visible through the quadrance-class map. -/
structure VisibleRotationProfile (rotations : List (Rotations.Basic.Rotation Scalar)) where
  /-- The retained ordered list of cached generator entries. -/ generators : List GeneratorEntry
  /-- The retained entries are exactly those computed from the supplied rotation list. -/ generators_eq : generators =
    generatorEntries rotations
  /-- The retained generator list has the original length. -/ generators_length : generators.length = rotations.length
  /-- Reading the retained rotations recovers the original ordered list. -/ generators_rotations : generators.map
    RotationProfiles.GeneratorEntry.rotation = rotations
  /-- The exact finite Boolean profile of the retained generator targets. -/ targetProfile :
    GeneratorProfiles.VisibleGeneratorProfile
    (generators.map RotationProfiles.GeneratorEntry.target)

constructive_injectivity VisibleRotationProfile

/-- Compute the finite chi-visible profile of one supplied rational rotation list, retaining every canonical inverse
representative used to obtain it. -/
@[expose] def visibleRotationProfile (rotations : List (Rotations.Basic.Rotation Scalar)) :
    VisibleRotationProfile rotations := by
  let generators := generatorEntries rotations
  exact
    { generators := generators
      generators_eq := rfl
      generators_length := generatorEntries_length rotations
      generators_rotations := generatorEntries_rotations rotations
      targetProfile := GeneratorProfiles.visibleGeneratorProfile
        (generators.map RotationProfiles.GeneratorEntry.target) }

/-- The retained finite chi-image has exactly two to the retained Boolean rank entries. -/
theorem visibleRotationProfile_image_length
    (rotations : List (Rotations.Basic.Rotation Scalar)) :
    (visibleRotationProfile rotations).targetProfile.span.entries.length =
      2 ^ (visibleRotationProfile rotations).targetProfile.span.rank :=
  (visibleRotationProfile rotations).targetProfile.span.length_eq

/-- The retained finite chi-image has no duplicate signature vectors. -/
theorem visibleRotationProfile_image_nodup
    (rotations : List (Rotations.Basic.Rotation Scalar)) :
    (((visibleRotationProfile rotations).targetProfile.span.entries.map
      Entry.vector)).Nodup :=
  (visibleRotationProfile rotations).targetProfile.span.vectors_nodup

set_option genInjectivity false in
/-- One occurrence in an arbitrary finite signed word over a supplied rotation profile. Membership is retained as a
certificate; `inverse = true` selects quaternion conjugation. -/
structure SignedLetter {rotations : List (Rotations.Basic.Rotation Scalar)}
    (profile : VisibleRotationProfile rotations) where
  /-- The cached generator selected for this word occurrence. -/ generator : GeneratorEntry
  /-- The selected generator belongs to the original retained profile. -/ member : generator ∈ profile.generators
  /-- Select the conjugate representative when true. -/ inverse : Bool

constructive_injectivity SignedLetter

/-- Select one cached canonical proportion with a displayed sign. -/
@[expose] def signedGeneratorProportion (generator : GeneratorEntry) (inverse : Bool) :
    Projective.Basic.NonNullProportion Scalar :=
  match inverse with
  | false => generator.proportion
  | true => NonNullProportion.conjugate generator.proportion

/-- Select the cached canonical proportion or its explicit conjugate. -/
@[expose] def selectedProportion {rotations : List (Rotations.Basic.Rotation Scalar)}
    {profile : VisibleRotationProfile rotations}
    (letter : SignedLetter profile) : Projective.Basic.NonNullProportion Scalar :=
  signedGeneratorProportion letter.generator letter.inverse

/-- Evaluate one arbitrary supplied finite signed word as a quaternion product. -/
@[expose] def signedWordProduct {rotations : List (Rotations.Basic.Rotation Scalar)}
    (profile : VisibleRotationProfile rotations) :
    List (SignedLetter profile) → Projective.Basic.NonNullProportion Scalar
  | [] => identityProportion
  | letter :: tail =>
      Projective.Basic.NonNullProportion.mul (selectedProportion letter)
        (signedWordProduct profile tail)

/-- Multiply the positive targets of the word. Inversion disappears here because a quaternion and its conjugate have
equal norm class. -/
@[expose] def signedWordTarget {rotations : List (Rotations.Basic.Rotation Scalar)}
    (profile : VisibleRotationProfile rotations) :
    List (SignedLetter profile) → Target
  | [] => proportionTarget identityProportion
  | letter :: tail =>
      PositiveSquareClassSignatures.mulTarget letter.generator.target
        (signedWordTarget profile tail)

/-- Selecting a generator or its conjugate preserves the generator's cached norm target. -/
theorem selectedProportion_target
    {rotations : List (Rotations.Basic.Rotation Scalar)}
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

/-- The norm target of a finite signed quaternion word equals the product of the cached generator targets. -/
theorem signedWordProduct_target
    {rotations : List (Rotations.Basic.Rotation Scalar)}
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

/-- Signature vectors of the occurrences in a supplied signed word. The sign does not alter a norm square class. -/
@[expose] def signedWordVectors {rotations : List (Rotations.Basic.Rotation Scalar)}
    (profile : VisibleRotationProfile rotations)
    (word : List (SignedLetter profile)) :
    List (Data.Vector.Boolean
      profile.targetProfile.finiteSupport.length) :=
  word.map fun letter =>
    GeneratorProfiles.signatureVector
      profile.targetProfile.finiteSupport letter.generator.target

/-- XOR evaluation of the finite signed word on the displayed shared prime support. -/
@[expose] def signedWordVector {rotations : List (Rotations.Basic.Rotation Scalar)}
    (profile : VisibleRotationProfile rotations)
    (word : List (SignedLetter profile)) :
    Data.Vector.Boolean
      profile.targetProfile.finiteSupport.length :=
  (signedWordVectors profile word).foldr Boolean.Basic.xor
    (Boolean.Basic.zero profile.targetProfile.finiteSupport.length)

/-- Every occurrence signature in a signed word belongs to the profile's retained generator vectors. -/
theorem signedWordVectors_mem
    {rotations : List (Rotations.Basic.Rotation Scalar)}
    (profile : VisibleRotationProfile rotations)
    (word : List (SignedLetter profile)) :
    ∀ vector ∈ signedWordVectors profile word,
      vector ∈ profile.targetProfile.vectors := by
  intro vector vectorMember
  rcases Map.mem_map.mp vectorMember with
    ⟨letter, letterMember, vectorEq⟩
  rw [profile.targetProfile.vectors_eq]
  apply Map.mem_map.mpr
  refine ⟨letter.generator.target, ?_, vectorEq⟩
  apply Map.mem_map.mpr
  exact ⟨letter.generator, letter.member, rfl⟩

/-- The signature of a signed-word target equals the XOR fold of its occurrence signatures. -/
theorem signedWordTarget_signature
    {rotations : List (Rotations.Basic.Rotation Scalar)}
    (profile : VisibleRotationProfile rotations) :
    ∀ word : List (SignedLetter profile),
      GeneratorProfiles.signatureVector
          profile.targetProfile.finiteSupport
          (signedWordTarget profile word) =
        signedWordVector profile word
  | [] => identity_signature_zero profile.targetProfile.finiteSupport
  | letter :: tail => by
      change GeneratorProfiles.signatureVector
          profile.targetProfile.finiteSupport
          (PositiveSquareClassSignatures.mulTarget letter.generator.target
            (signedWordTarget profile tail)) =
        Boolean.Basic.xor
          (GeneratorProfiles.signatureVector
            profile.targetProfile.finiteSupport letter.generator.target)
          (signedWordVector profile tail)
      rw [GeneratorProfiles.signatureVector_mul,
        signedWordTarget_signature profile tail]

/-- Folding an arbitrary supplied finite signed rotation word and folding its finite prime-parity signatures commute
with the quadrance-class map. -/
theorem signedWordProduct_signature
    {rotations : List (Rotations.Basic.Rotation Scalar)}
    (profile : VisibleRotationProfile rotations)
    (word : List (SignedLetter profile)) :
    GeneratorProfiles.signatureVector
        profile.targetProfile.finiteSupport
        (proportionTarget (signedWordProduct profile word)) =
      signedWordVector profile word := by
  rw [signedWordProduct_target profile word]
  exact signedWordTarget_signature profile word

/-- Every arbitrary supplied finite signed word is classified by one retained entry of the exact finite chi-image. -/
theorem classifySignedWord
    {rotations : List (Rotations.Basic.Rotation Scalar)}
    (profile : VisibleRotationProfile rotations)
    (word : List (SignedLetter profile)) :
    ∃ entry ∈ profile.targetProfile.span.entries,
      signedWordVector profile word = entry.vector :=
  profile.targetProfile.span.classifyXorWord
    (signedWordVectors profile word)
    (signedWordVectors_mem profile word)

set_option genInjectivity false in
/-- A compact signed word aligned with the supplied generator list. A false choice omits that generator; a true choice
uses it once in the displayed direction. This finite normal form is sufficient for every element of the Boolean
chi-image. -/
structure SignedSelectionWord {rotations : List (Rotations.Basic.Rotation Scalar)}
    (profile : VisibleRotationProfile rotations) where
  /-- The displayed Boolean choices selecting generator occurrences. -/ choices : List Bool
  /-- The choice list is aligned with the retained generator list. -/ choices_length : choices.length =
    profile.generators.length
  /-- The displayed inversion flags for the selected generators. -/ inverses : List Bool
  /-- The inversion list is aligned with the retained generator list. -/ inverses_length : inverses.length =
    profile.generators.length

constructive_injectivity SignedSelectionWord

/-- Evaluate aligned selection and inversion lists against cached generator entries.

Selected entries contribute their representative or conjugate; unselected entries are skipped, and evaluation stops at
the first exhausted input list. -/
@[expose] def selectionProductFromFinite
    (generators : List GeneratorEntry) (choices inverses : List Bool) :
    Projective.Basic.NonNullProportion Scalar :=
  List.casesOn generators identityProportion (fun generator generators =>
    List.casesOn choices identityProportion (fun choice choices =>
      List.casesOn inverses identityProportion (fun inverse inverses =>
        (Bool.casesOn (motive := fun _ => Unit → Projective.Basic.NonNullProportion Scalar) choice
          (fun _ : Unit => selectionProductFromFinite generators choices inverses)
          (fun _ : Unit => NonNullProportion.mul
            (signedGeneratorProportion generator inverse)
            (selectionProductFromFinite generators choices inverses))) ())))
termination_by structural generators

/-- Evaluate the compact signed selection as an explicit finite quaternion product. -/
@[expose] def signedSelectionProduct {rotations : List (Rotations.Basic.Rotation Scalar)}
    (profile : VisibleRotationProfile rotations)
    (word : SignedSelectionWord profile) : Projective.Basic.NonNullProportion Scalar :=
  selectionProductFromFinite profile.generators word.choices word.inverses

/-- A cached generator and its conjugate have the same cached target. -/
private theorem signedGeneratorProportion_target
    (generator : GeneratorEntry) (inverse : Bool) :
    proportionTarget (signedGeneratorProportion generator inverse) =
      generator.target := by
  cases inverse with
  | false => exact generator.target_eq.symm
  | true =>
      exact (proportionTarget_conjugate generator.proportion).trans
        generator.target_eq.symm

/-- An aligned signed selection has the Boolean signature computed from its choices and cached generator targets. -/
private theorem selectionProductFrom_signature (finiteSupport : List Nat) :
    ∀ (generators : List GeneratorEntry)
      (choices inverses : List Bool),
      choices.length = generators.length →
      inverses.length = generators.length →
      GeneratorProfiles.signatureVector finiteSupport
          (proportionTarget
            (selectionProductFromFinite generators choices inverses)) =
        Boolean.Basic.evaluate choices
          (generators.map fun generator =>
            GeneratorProfiles.signatureVector finiteSupport
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
                  change GeneratorProfiles.signatureVector finiteSupport
                      (proportionTarget
                        (NonNullProportion.mul
                          (signedGeneratorProportion generator inverse)
                          (selectionProductFromFinite generators tailChoices
                            tailInverses))) =
                    Boolean.Basic.xor
                      (GeneratorProfiles.signatureVector finiteSupport
                        generator.target)
                      (Boolean.Basic.evaluate tailChoices
                        (generators.map fun tailGenerator =>
                          GeneratorProfiles.signatureVector finiteSupport
                            tailGenerator.target))
                  rw [proportionTarget_mul,
                    signedGeneratorProportion_target,
                    GeneratorProfiles.signatureVector_mul,
                    selectionProductFrom_signature finiteSupport generators
                      tailChoices tailInverses tailChoicesLength
                      tailInversesLength]

/-- The compact signed-word product has exactly the Boolean signature obtained by evaluating its choices against the
cached generator vectors. -/
theorem signedSelectionProduct_signature
    {rotations : List (Rotations.Basic.Rotation Scalar)}
    (profile : VisibleRotationProfile rotations)
    (word : SignedSelectionWord profile) :
    GeneratorProfiles.signatureVector
        profile.targetProfile.finiteSupport
        (proportionTarget
          (signedSelectionProduct profile word)) =
      Boolean.Basic.evaluate word.choices
        profile.targetProfile.vectors := by
  rw [profile.targetProfile.vectors_eq]
  have mappedVectors :
      (profile.generators.map RotationProfiles.GeneratorEntry.target).map
          (GeneratorProfiles.signatureVector
            profile.targetProfile.finiteSupport) =
        profile.generators.map fun generator =>
          GeneratorProfiles.signatureVector
            profile.targetProfile.finiteSupport generator.target :=
    Map.map_map (GeneratorProfiles.signatureVector profile.targetProfile.finiteSupport)
      RotationProfiles.GeneratorEntry.target profile.generators
  rw [mappedVectors]
  unfold signedSelectionProduct
  exact selectionProductFrom_signature profile.targetProfile.finiteSupport
    profile.generators word.choices word.inverses word.choices_length
    word.inverses_length

/-- Turn the Boolean choices retained by an image entry into an explicit forward-only signed generator word. -/
@[expose] def entrySignedWord
    {rotations : List (Rotations.Basic.Rotation Scalar)}
    (profile : VisibleRotationProfile rotations)
    (entry : Boolean.Basic.Entry
      profile.targetProfile.vectors) : SignedSelectionWord profile := by
  have vectorsLength : profile.targetProfile.vectors.length =
      profile.generators.length := by
    rw [profile.targetProfile.vectors_eq, Map.length_map, Map.length_map]
  exact
    { choices := entry.choices
      choices_length := entry.choices_length.trans vectorsLength
      inverses := List.replicate profile.generators.length false
      inverses_length := Replicate.length_replicate profile.generators.length false }

/-- Every listed finite-image signature retains a signed generator word whose explicit quaternion product realizes that
signature. -/
theorem entrySignedWord_realizes
    {rotations : List (Rotations.Basic.Rotation Scalar)}
    (profile : VisibleRotationProfile rotations)
    (entry : Boolean.Basic.Entry
      profile.targetProfile.vectors) :
    GeneratorProfiles.signatureVector
        profile.targetProfile.finiteSupport
        (proportionTarget
          (signedSelectionProduct profile (entrySignedWord profile entry))) =
      entry.vector := by
  rw [signedSelectionProduct_signature]
  exact entry.evaluates

end

end Purelib.Geometry.Rotations.Rational.Generators.Profile.RotationProfiles

section
open Purelib
open Purelib.Data.Vector
open Purelib.LinearAlgebra.Span
open Purelib.LinearAlgebra.Span.Boolean.Basic
open Purelib.NumberTheory.SquareClass
open Purelib.NumberTheory.SquareClass.Rational.Span
open Purelib.NumberTheory.SquareClass.Rational.Signature.PositiveSquareClassSignatures
open _root_.Purelib.NumberTheory.SquareClass.Rational.Signature renaming Positive -> Signature
open Purelib.Algebra.Quaternion
open Purelib.Algebra.Quaternion.Projective.Basic
open Purelib.Geometry.Rotations.Rational.Generators.Profile
namespace Purelib.Geometry.Rotations.Rational.Generators.Profile.RotationProfiles

/-- The fixed rational identity proportion equals the generic identity built from any non-null witness. -/
public theorem
  identityProportion_eq_identity
    (witness : Projective.Basic.NonNullProportion
      Scalar) :
    identityProportion =
      NonNullProportion.identity witness := by
  apply NonNullProportion.ext (K := Scalar) <;>
    rfl

end Purelib.Geometry.Rotations.Rational.Generators.Profile.RotationProfiles
end
