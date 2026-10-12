module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Geometry.Rotations.Projective.Action
import Purelib.NumberTheory.SquareClass.Rational.Signature
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.SquareClass.Basic
public import Purelib.Algebra.Quaternion.Projective.UnitObstruction
import Purelib.Data.List.Map
import Purelib.Data.Vector.Boolean.Basic
import Purelib.LinearAlgebra.Span.Boolean.Basic
import Purelib.LinearAlgebra.Span.Boolean.Search

import Purelib.Algebra.Quaternion.Projective.Basic
import Purelib.Geometry.Rotations.Projective.Correspondence
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.NumberTheory.SquareClass.Rational.Span
public import Purelib.Geometry.Rotations.Rational.Generators.Profile
import Purelib.Geometry.Rotations.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.NumberTheory.SquareClass.Rational.Basic
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Algebra.Field.SquareClass.Basic

open Purelib.Algebra.Quaternion

open Purelib.Algebra.Quaternion.Projective.Basic

open Purelib.Algebra.Quaternion.Projective.UnitObstruction

open Purelib.Algebra.Quaternion.Projective.UnitObstruction.NonNullProportion

open Purelib.Data.List

open Purelib.Data.Vector

open Purelib.Geometry

open Purelib.Geometry.Rotations.Projective.Action

open Purelib.Geometry.Rotations.Projective.Correspondence

open Purelib.Geometry.Rotations.Rational.Generators.Profile

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Span

open Purelib.LinearAlgebra.Span.Boolean

open Purelib.LinearAlgebra.Span.Boolean.Basic

open Purelib.LinearAlgebra.Span.Boolean.Search

open Purelib.NumberTheory.SquareClass.Rational.Span

@[expose] public section

/-!
# Finite-query classification of finitely generated rational rotation groups

Problem 70 asks for the finitely generated subgroups visible through the
quadrance-class map.  This module gives the strongest finite-only reading of
that request.  A supplied finite generator list determines finite signed
words, exact quaternion and rotation-matrix evaluation, an exact finite
`chi`-image, and exact kernel-coset tests.  It deliberately never forms the
set of all words, a completed generated subgroup, or an infinite quotient.
-/

namespace Purelib.Geometry.Rotations.Rational.Generators

open Purelib.Geometry.Rotations.Basic

open Purelib.LinearAlgebra.Coordinates3

section _root_.Purelib.Geometry.Rotations.Rational.Generators.Classification.GeneratedSubgroups

open Purelib.NumberTheory.SquareClass.Rational.Signature.PositiveSquareClassSignatures
open _root_.Purelib.NumberTheory.SquareClass.Rational.Signature renaming Positive -> Signature

namespace Classification.GeneratedSubgroups

/-- The constructive rational field of the finite signed-word classifier. -/
abbrev Scalar := RotationProfiles.Scalar

/-- A finite signed word whose occurrences retain membership in the supplied rotation profile. -/
abbrev Word {rotations : List (Rotations.Basic.Rotation
  Scalar)}
    (profile : RotationProfiles.VisibleRotationProfile rotations) :=
  List (RotationProfiles.SignedLetter profile)

/-- The fixed rational identity proportion is a left unit. -/
@[simp] theorem identityProportion_mul
    (proportion : Projective.Basic.NonNullProportion
      Scalar) :
    NonNullProportion.mul RotationProfiles.identityProportion
      proportion = proportion := by
  rw
    [Purelib.Geometry.Rotations.Rational.Generators.Profile.RotationProfiles.identityProportion_eq_identity
    proportion,
    NonNullProportion.identity_mul]

/-- The fixed rational identity proportion is a right unit. -/
@[simp] theorem mul_identityProportion
    (proportion : Projective.Basic.NonNullProportion
      Scalar) :
    NonNullProportion.mul proportion
      RotationProfiles.identityProportion = proportion := by
  rw
    [Purelib.Geometry.Rotations.Rational.Generators.Profile.RotationProfiles.identityProportion_eq_identity
    proportion,
    NonNullProportion.mul_identity]

/-- Concatenation is the finite-word multiplication operation. -/
theorem signedWordProduct_append
    {rotations : List (Rotations.Basic.Rotation
      Scalar)}
    (profile : RotationProfiles.VisibleRotationProfile rotations) :
    ∀ left right : Word profile,
      RotationProfiles.signedWordProduct profile (left ++ right) =
        NonNullProportion.mul
          (RotationProfiles.signedWordProduct profile left)
          (RotationProfiles.signedWordProduct profile right)
  | [], right => by
      change RotationProfiles.signedWordProduct profile right =
        NonNullProportion.mul RotationProfiles.identityProportion
          (RotationProfiles.signedWordProduct profile right)
      rw [identityProportion_mul]
  | letter :: tail, right => by
      change NonNullProportion.mul
          (RotationProfiles.selectedProportion letter)
          (RotationProfiles.signedWordProduct profile (tail ++ right)) =
        NonNullProportion.mul
          (NonNullProportion.mul
            (RotationProfiles.selectedProportion letter)
            (RotationProfiles.signedWordProduct profile tail))
          (RotationProfiles.signedWordProduct profile right)
      rw [signedWordProduct_append
        profile tail right]
      exact (NonNullProportion.mul_assoc
        (RotationProfiles.selectedProportion letter)
        (RotationProfiles.signedWordProduct profile tail)
        (RotationProfiles.signedWordProduct profile right)).symm

/-- The finite `chi` evaluator sends word concatenation to vector XOR. -/
theorem signedWordVector_append
    {rotations : List (Rotations.Basic.Rotation
      Scalar)}
    (profile : RotationProfiles.VisibleRotationProfile rotations) :
    ∀ left right : Word profile,
      RotationProfiles.signedWordVector profile (left ++ right) =
        Boolean.Basic.xor
          (RotationProfiles.signedWordVector profile left)
          (RotationProfiles.signedWordVector profile right)
  | [], right => by
      change RotationProfiles.signedWordVector profile right =
        Boolean.Basic.xor
          (Boolean.Basic.zero
            profile.targetProfile.finiteSupport.length)
          (RotationProfiles.signedWordVector profile right)
      exact (Boolean.Basic.zero_xor _).symm
  | letter :: tail, right => by
      change Boolean.Basic.xor
          (GeneratorProfiles.signatureVector
            profile.targetProfile.finiteSupport letter.generator.target)
          (RotationProfiles.signedWordVector profile (tail ++ right)) =
        Boolean.Basic.xor
          (Boolean.Basic.xor
            (GeneratorProfiles.signatureVector
              profile.targetProfile.finiteSupport letter.generator.target)
            (RotationProfiles.signedWordVector profile tail))
          (RotationProfiles.signedWordVector profile right)
      rw [signedWordVector_append
        profile tail right]
      exact (Boolean.Basic.xor_assoc _ _ _).symm

/-- Toggle one displayed generator occurrence between the forward and inverse directions. -/
def inverseLetter {rotations : List (Rotations.Basic.Rotation
  Scalar)}
    {profile : RotationProfiles.VisibleRotationProfile rotations}
    (letter : RotationProfiles.SignedLetter profile) :
    RotationProfiles.SignedLetter profile where
  generator := letter.generator
  member := letter.member
  inverse := !letter.inverse

/-- Toggling an occurrence's inversion flag conjugates its selected quaternion representative. -/
theorem selectedProportion_inverseLetter
    {rotations : List (Rotations.Basic.Rotation
      Scalar)}
    {profile : RotationProfiles.VisibleRotationProfile rotations}
    (letter : RotationProfiles.SignedLetter profile) :
    RotationProfiles.selectedProportion
      (inverseLetter letter) =
      NonNullProportion.conjugate
        (RotationProfiles.selectedProportion letter) := by
  cases letter with
  | mk generator member inverse =>
      cases inverse with
      | false => rfl
      | true =>
          exact (NonNullProportion.conjugate_conjugate
            generator.proportion).symm

/-- Reverse a finite signed word and toggle every sign. -/
def inverseWord {rotations : List (Basic.Rotation
  Scalar)}
    {profile : Purelib.Geometry.Rotations.Rational.Generators.Profile.RotationProfiles.VisibleRotationProfile rotations}
      :
    Word profile →
      Word profile
  | [] => []
  | letter :: tail => inverseWord tail
    ++ [inverseLetter letter]

/-- The explicit inverse-word algorithm evaluates to quaternion conjugation. -/
theorem signedWordProduct_inverseWord
    {rotations : List (Rotations.Basic.Rotation
      Scalar)}
    (profile : RotationProfiles.VisibleRotationProfile rotations) :
    ∀ word : Word profile,
      RotationProfiles.signedWordProduct profile
        (inverseWord word) =
        NonNullProportion.conjugate
          (RotationProfiles.signedWordProduct profile word)
  | [] => by
      apply NonNullProportion.ext (K := Scalar)
        <;> rfl
  | letter :: tail => by
      change RotationProfiles.signedWordProduct profile
          (inverseWord tail ++
            [inverseLetter letter]) =
        NonNullProportion.conjugate
          (NonNullProportion.mul
            (RotationProfiles.selectedProportion letter)
            (RotationProfiles.signedWordProduct profile tail))
      rw [signedWordProduct_append,
        signedWordProduct_inverseWord,
        show RotationProfiles.signedWordProduct profile
            [inverseLetter letter] =
          NonNullProportion.conjugate
            (RotationProfiles.selectedProportion letter) by
          change NonNullProportion.mul
              (RotationProfiles.selectedProportion
                (inverseLetter letter))
              RotationProfiles.identityProportion = _
          rw [mul_identityProportion,
            selectedProportion_inverseLetter],
        NonNullProportion.conjugate_mul_reverse]

/-- Inversion fixes the `chi` vector because every rational square class has order at most two. -/
theorem signedWordVector_inverseWord
    {rotations : List (Rotations.Basic.Rotation
      Scalar)}
    (profile : RotationProfiles.VisibleRotationProfile rotations) :
    ∀ word : Word profile,
      RotationProfiles.signedWordVector profile
        (inverseWord word) =
        RotationProfiles.signedWordVector profile word
  | [] => rfl
  | letter :: tail => by
      rw [inverseWord,
        signedWordVector_append,
        signedWordVector_inverseWord]
      change Boolean.Basic.xor
          (RotationProfiles.signedWordVector profile tail)
          (Boolean.Basic.xor
            (GeneratorProfiles.signatureVector
              profile.targetProfile.finiteSupport letter.generator.target)
            (Boolean.Basic.zero
              profile.targetProfile.finiteSupport.length)) =
        Boolean.Basic.xor
          (GeneratorProfiles.signatureVector
            profile.targetProfile.finiteSupport letter.generator.target)
          (RotationProfiles.signedWordVector profile tail)
      rw [Boolean.Basic.xor_zero,
        Boolean.Basic.xor_comm]

/-- Every prime in the computed norm signature of a finite word already lies in the cached union of the generator
supports. -/
theorem signedWordTarget_primes_subset
    {rotations : List (Rotations.Basic.Rotation
      Scalar)}
    (profile : RotationProfiles.VisibleRotationProfile rotations) :
    ∀ (word : Word profile) (prime : Nat),
      prime ∈ (compute
        (RotationProfiles.signedWordTarget profile word)).primes →
      prime ∈ profile.targetProfile.finiteSupport
  | [], prime, member => by
      change prime ∈ (compute
        (RotationProfiles.proportionTarget
          RotationProfiles.identityProportion)).primes at member
      rw [RotationProfiles.identity_target_primes_empty] at member
      nomatch member
  | letter :: tail, prime, member => by
      have productSupport := compute_mulTarget_support
        letter.generator.target
        (RotationProfiles.signedWordTarget profile tail) prime
      have xorMember := productSupport.mp member
      rcases (mem_xorSupport_iff prime _ _).mp xorMember with
        generatorOnly | tailOnly
      · rw [profile.targetProfile.finiteSupport_eq]
        apply GeneratorProfiles.target_primes_subset_support
          (target := letter.generator.target)
        · apply Map.mem_map.mpr
          exact ⟨letter.generator, letter.member, rfl⟩
        · exact generatorOnly.1
      · exact
          signedWordTarget_primes_subset
          profile tail prime tailOnly.1

/-- On a support containing both complete finite signatures, equality of Boolean vectors is exactly rational
square-class equivalence. -/
theorem signatureVector_eq_iff_equivalent_of_subsets
    (finiteSupport : List Nat)
    (left right : GeneratorProfiles.Target)
    (leftSubset : ∀ prime, prime ∈ (compute left).primes →
      prime ∈ finiteSupport)
    (rightSubset : ∀ prime, prime ∈ (compute right).primes →
      prime ∈ finiteSupport) :
    GeneratorProfiles.signatureVector finiteSupport left =
        GeneratorProfiles.signatureVector finiteSupport right ↔
      left.representative.Equivalent right.representative := by
  let leftSignature := compute left
  let rightSignature := compute right
  constructor
  · intro vectorEqual
    have bitsEqual := congrArg Data.Vector.Boolean.bits vectorEqual
    change GeneratorProfiles.signatureBits finiteSupport
        leftSignature.primes =
      GeneratorProfiles.signatureBits finiteSupport
        rightSignature.primes at bitsEqual
    have sameMembers : ∀ prime,
        prime ∈ leftSignature.primes ↔ prime ∈ rightSignature.primes := by
      intro prime
      constructor
      · intro leftMember
        have supportMember := leftSubset prime leftMember
        have containsEqual :=
          Purelib.NumberTheory.SquareClass.Rational.Span.GeneratorProfiles.natContains_eq_of_signatureBits_eq
          prime
          finiteSupport leftSignature.primes rightSignature.primes
          supportMember bitsEqual
        have leftTrue :=
          (natContains_eq_true_iff prime leftSignature.primes).mpr leftMember
        apply (natContains_eq_true_iff prime rightSignature.primes).mp
        rw [← containsEqual]
        exact leftTrue
      · intro rightMember
        have supportMember := rightSubset prime rightMember
        have containsEqual :=
          Purelib.NumberTheory.SquareClass.Rational.Span.GeneratorProfiles.natContains_eq_of_signatureBits_eq
          prime
          finiteSupport leftSignature.primes rightSignature.primes
          supportMember bitsEqual
        have rightTrue :=
          (natContains_eq_true_iff prime rightSignature.primes).mpr rightMember
        apply (natContains_eq_true_iff prime leftSignature.primes).mp
        rw [containsEqual]
        exact rightTrue
    have displayedEquivalent := (primeSupportEquivalent_iff
      leftSignature.primes_prime rightSignature.primes_prime
      leftSignature.primes_nodup rightSignature.primes_nodup).mpr sameMembers
    have kernelEquivalent :
        (positiveNaturalClass leftSignature.kernel
          leftSignature.kernel_positive).Equivalent
        (positiveNaturalClass rightSignature.kernel
          rightSignature.kernel_positive) := by
      simpa only [leftSignature.kernel_eq, rightSignature.kernel_eq] using
        displayedEquivalent
    exact SquareClassRepresentative.equivalent_trans
      (SquareClassRepresentative.equivalent_symm leftSignature.equivalent)
      (SquareClassRepresentative.equivalent_trans kernelEquivalent
        rightSignature.equivalent)
  · intro equivalent
    have kernelEquivalent :
        (positiveNaturalClass leftSignature.kernel
          leftSignature.kernel_positive).Equivalent
        (positiveNaturalClass rightSignature.kernel
          rightSignature.kernel_positive) :=
      SquareClassRepresentative.equivalent_trans leftSignature.equivalent
        (SquareClassRepresentative.equivalent_trans equivalent
          (SquareClassRepresentative.equivalent_symm
            rightSignature.equivalent))
    have displayedEquivalent :
        (positiveNaturalClass leftSignature.primes.prod
          (by
              simpa only [leftSignature.kernel_eq]
                using leftSignature.kernel_positive)).Equivalent
        (positiveNaturalClass rightSignature.primes.prod
          (by
              simpa only [rightSignature.kernel_eq]
                using rightSignature.kernel_positive)) := by
      simpa only [leftSignature.kernel_eq, rightSignature.kernel_eq] using
        kernelEquivalent
    have sameMembers := (primeSupportEquivalent_iff
      leftSignature.primes_prime rightSignature.primes_prime
      leftSignature.primes_nodup rightSignature.primes_nodup).mp
        displayedEquivalent
    apply Data.Vector.Boolean.ext
    exact
      Purelib.NumberTheory.SquareClass.Rational.Span.GeneratorProfiles.signatureBits_eq_of_same_members
      finiteSupport
      leftSignature.primes rightSignature.primes sameMembers

set_option genInjectivity false in
/-- Cached normalizer for one rational projective proportion. Scaling by this explicit inverse square factor changes its
norm to the computed natural kernel, whether or not that kernel is one. -/
structure KernelNormalization (proportion : Projective.Basic.NonNullProportion
  Scalar) where
  /-- The cached finite prime signature of the proportion's positive norm target. -/ signature : Signature
    (RotationProfiles.proportionTarget proportion)
  /-- The retained signature is exactly the result of the canonical finite computation. -/ signature_eq : signature =
    compute
    (RotationProfiles.proportionTarget proportion)
  /-- The cached rational normalization scalar. -/ factor :
    Scalar
  /-- The factor is exactly the inverse of the retained signature square factor. -/ factor_eq : factor =
    signature.squareFactor⁻¹
  /-- The retained normalization scalar is nonzero. -/ factorNonzero : factor ≠ 0
  /-- Scaling by the retained factor makes the quaternion norm equal the retained natural kernel. -/ norm_eq_kernel :
    (Proportion.scale factor proportion.toProportion).norm =
      (signature.kernel : Scalar)

constructive_injectivity KernelNormalization

/-- Compute and retain the finite square-class normalizer. -/
def kernelNormalization (proportion : Projective.Basic.NonNullProportion
  Scalar) :
    KernelNormalization proportion := by
  let signature := compute
    (RotationProfiles.proportionTarget proportion)
  let factor := signature.squareFactor⁻¹
  have factorNonzero : factor ≠ 0 :=
    Algebra.Field.ExplicitField.inv_ne_zero signature.squareFactor_nonzero
  refine
    { signature := signature
      signature_eq := rfl
      factor := factor
      factor_eq := rfl
      factorNonzero := factorNonzero
      norm_eq_kernel := ?_ }
  rw [Proportion.norm_scale]
  change factor ^ 2 *
      (RotationProfiles.proportionTarget proportion).representative.value =
    (signature.kernel : Scalar)
  rw [signature.value_eq_squareFactor_sq_mul_kernel]
  have cancel := Algebra.Field.ExplicitField.mul_inv_cancel signature.squareFactor
    signature.squareFactor_nonzero
  unfold factor
  calc
    signature.squareFactor⁻¹ ^ 2 *
        (signature.squareFactor ^ 2 * (signature.kernel :
          Scalar)) =
      (signature.squareFactor * signature.squareFactor⁻¹) ^ 2 *
        (signature.kernel : Scalar) := by ring1
    _ = (signature.kernel : Scalar) := by
      rw [cancel]
      ring1

/-- When the computed kernel is one, the cached normalizer becomes an executable norm-one representative certificate. -/
def unitRepresentativeCertificateOfKernelEqOne
    (proportion : Projective.Basic.NonNullProportion
      Scalar)
    (kernelOne :
      (compute (RotationProfiles.proportionTarget proportion)).kernel =
        1) :
    NonNullProportion.UnitRepresentativeCertificate proportion := by
  let normalization := kernelNormalization
    proportion
  refine
    { factor := normalization.factor
      factorNonzero := normalization.factorNonzero
      normOne := ?_ }
  calc
    (Proportion.scale normalization.factor proportion.toProportion).norm =
        (normalization.signature.kernel :
          Scalar) :=
      normalization.norm_eq_kernel
    _ = (1 : Scalar) := by
      rw [normalization.signature_eq, kernelOne]
      rfl

/-- Over the rationals, kernel membership is decided exactly by the cached natural odd-prime kernel. The reverse
implication returns the explicit normalizing scalar above. -/
theorem hasUnitRepresentative_iff_kernel_eq_one
    (proportion : Projective.Basic.NonNullProportion
      Scalar) :
    (QuaternionObstruction.HasUnitRepresentative proportion) ↔
      (compute
        (RotationProfiles.proportionTarget proportion)).kernel = 1 := by
  constructor
  · intro unit
    have trivialClass :=
      (NonNullProportion.hasUnitRepresentative_iff_quadranceClass_trivial
        proportion).mp unit
    have unitClassEq : (NonNullProportion.unitSquareClass proportion) =
      Purelib.NumberTheory.SquareClass.Rational.Span.GeneratorProfiles.oneTarget.representative
      := by
      apply SquareClassRepresentative.ext
      rfl
    have equivalentOne :
        SquareClassRepresentative.Equivalent
          (RotationProfiles.proportionTarget proportion).representative

            Purelib.NumberTheory.SquareClass.Rational.Span.GeneratorProfiles.oneTarget.representative
            := by
      rw [← unitClassEq]
      exact trivialClass
    have kernelsEqual := (equivalent_iff_kernel_eq
      (compute (RotationProfiles.proportionTarget proportion))
      (compute
        Purelib.NumberTheory.SquareClass.Rational.Span.GeneratorProfiles.oneTarget)).mp
        equivalentOne
    exact kernelsEqual.trans
      Purelib.NumberTheory.SquareClass.Rational.Span.GeneratorProfiles.oneTarget_kernel_eq_one
  · intro kernelOne
    exact UnitRepresentativeCertificate.hasUnitRepresentative

        (unitRepresentativeCertificateOfKernelEqOne
        proportion kernelOne)

/-- A signed word lies in the restricted unit-quaternion kernel exactly when its complete finite XOR signature is zero.
-/
theorem signedWord_hasUnitRepresentative_iff_vector_zero
    {rotations : List (Rotations.Basic.Rotation
      Scalar)}
    (profile : RotationProfiles.VisibleRotationProfile rotations)
    (word : Word profile) :
    QuaternionObstruction.HasUnitRepresentative
        (RotationProfiles.signedWordProduct profile word) ↔
      RotationProfiles.signedWordVector profile word =
        Boolean.Basic.zero
          profile.targetProfile.finiteSupport.length := by
  have kernelCriterion :=
    hasUnitRepresentative_iff_kernel_eq_one
    (RotationProfiles.signedWordProduct profile word)
  have kernelTarget :
      (compute (RotationProfiles.proportionTarget
        (RotationProfiles.signedWordProduct profile word))).kernel =
      (compute (RotationProfiles.signedWordTarget profile word)).kernel := by
    rw [RotationProfiles.signedWordProduct_target]
  have vectorCriterion :=
    Purelib.NumberTheory.SquareClass.Rational.Span.GeneratorProfiles.signatureVector_eq_zero_iff_primes_empty_of_subset
    profile.targetProfile.finiteSupport
    (RotationProfiles.signedWordTarget profile word)
    (Geometry.Rotations.Rational.Generators.Classification.GeneratedSubgroups.signedWordTarget_primes_subset profile
      word)
  constructor
  · intro representative
    have kernelOne := kernelCriterion.mp representative
    have targetKernelOne := kernelTarget.symm.trans kernelOne
    have primesEmpty := (compute
      (RotationProfiles.signedWordTarget profile word)).kernel_eq_one_iff_primes_eq_nil.mp targetKernelOne
    have vectorZero := vectorCriterion.mpr primesEmpty
    rw [RotationProfiles.signedWordTarget_signature] at vectorZero
    exact vectorZero
  · intro vectorZero
    have targetVectorZero : GeneratorProfiles.signatureVector
        profile.targetProfile.finiteSupport
        (RotationProfiles.signedWordTarget profile word) =
      Boolean.Basic.zero profile.targetProfile.finiteSupport.length := by
      rw [RotationProfiles.signedWordTarget_signature]
      exact vectorZero
    have primesEmpty := vectorCriterion.mp targetVectorZero
    have targetKernelOne := (compute
      (RotationProfiles.signedWordTarget profile word)).kernel_eq_one_iff_primes_eq_nil.mpr primesEmpty
    exact kernelCriterion.mpr (kernelTarget.trans targetKernelOne)

/-- Two finite words represent the same coset of the restricted kernel exactly when their finite `chi` vectors agree. -/
theorem signedWords_sameKernelCoset_iff_vector_eq
    {rotations : List (Rotations.Basic.Rotation
      Scalar)}
    (profile : RotationProfiles.VisibleRotationProfile rotations)
    (left right : Word profile) :
    NonNullProportion.InSameUnitKernelCoset
        (RotationProfiles.signedWordProduct profile left)
        (RotationProfiles.signedWordProduct profile right) ↔
      RotationProfiles.signedWordVector profile left =
        RotationProfiles.signedWordVector profile right := by
  have cosetCriterion := NonNullProportion.inSameUnitKernelCoset_iff_quadranceClass_equivalent
    (RotationProfiles.signedWordProduct profile left)
    (RotationProfiles.signedWordProduct profile right)
  have vectorCriterion :=
    signatureVector_eq_iff_equivalent_of_subsets
    profile.targetProfile.finiteSupport
    (RotationProfiles.signedWordTarget profile left)
    (RotationProfiles.signedWordTarget profile right)
    (Geometry.Rotations.Rational.Generators.Classification.GeneratedSubgroups.signedWordTarget_primes_subset profile
      left)
    (Geometry.Rotations.Rational.Generators.Classification.GeneratedSubgroups.signedWordTarget_primes_subset profile
      right)
  constructor
  · intro coset
    have equivalent := cosetCriterion.mp coset
    change SquareClassRepresentative.Equivalent
      (RotationProfiles.proportionTarget
        (RotationProfiles.signedWordProduct profile left)).representative
      (RotationProfiles.proportionTarget
        (RotationProfiles.signedWordProduct profile right)).representative at equivalent
    rw [RotationProfiles.signedWordProduct_target,
      RotationProfiles.signedWordProduct_target] at equivalent
    have vectorsEqual := vectorCriterion.mpr equivalent
    rw [RotationProfiles.signedWordTarget_signature,
      RotationProfiles.signedWordTarget_signature] at vectorsEqual
    exact vectorsEqual
  · intro vectorsEqual
    have targetVectorsEqual : GeneratorProfiles.signatureVector
        profile.targetProfile.finiteSupport (RotationProfiles.signedWordTarget profile left) =
      GeneratorProfiles.signatureVector
        profile.targetProfile.finiteSupport (RotationProfiles.signedWordTarget profile right) := by
      rw [RotationProfiles.signedWordTarget_signature,
        RotationProfiles.signedWordTarget_signature]
      exact vectorsEqual
    have equivalent := vectorCriterion.mp targetVectorsEqual
    apply cosetCriterion.mpr
    change SquareClassRepresentative.Equivalent
      (RotationProfiles.proportionTarget
        (RotationProfiles.signedWordProduct profile left)).representative
      (RotationProfiles.proportionTarget
        (RotationProfiles.signedWordProduct profile right)).representative
    rw [RotationProfiles.signedWordProduct_target,
      RotationProfiles.signedWordProduct_target]
    exact equivalent

/-- Exact finite comparison of two word evaluations as rotations. -/
inductive ElementComparison
    {rotations : List (Rotations.Basic.Rotation
      Scalar)}
    (profile : RotationProfiles.VisibleRotationProfile rotations)
    (left right : Word profile) : Type
  /-- The two evaluated finite words have equal rational rotation matrices. -/ | same (matrix_eq :
      (NonNullProportion.rotationMatrix (RotationProfiles.signedWordProduct profile left)) =
        (NonNullProportion.rotationMatrix (RotationProfiles.signedWordProduct profile right)))
  /-- The two evaluated finite words have unequal rational rotation matrices. -/ | different (matrix_ne :
      (NonNullProportion.rotationMatrix (RotationProfiles.signedWordProduct profile left)) ≠
        (NonNullProportion.rotationMatrix (RotationProfiles.signedWordProduct profile right)))

/-- Compare all nine rational matrix entries; no enumeration of other words is involved. -/
def compareElements
    {rotations : List (Rotations.Basic.Rotation
      Scalar)}
    (profile : RotationProfiles.VisibleRotationProfile rotations)
    (left right : Word profile) :
      ElementComparison profile left right :=
  if equal :
      (NonNullProportion.rotationMatrix (RotationProfiles.signedWordProduct profile left)) =
        (NonNullProportion.rotationMatrix (RotationProfiles.signedWordProduct profile right))
  then Geometry.Rotations.Rational.Generators.Classification.GeneratedSubgroups.ElementComparison.same equal
  else Geometry.Rotations.Rational.Generators.Classification.GeneratedSubgroups.ElementComparison.different equal

/-- Exact matrix equality is also exactly projective equality of the two evaluated quaternion products. -/
theorem signedWords_sameRotation_iff_equivalent
    {rotations : List (Rotations.Basic.Rotation
      Scalar)}
    (profile : RotationProfiles.VisibleRotationProfile rotations)
    (left right : Word profile) :
    (NonNullProportion.rotationMatrix (RotationProfiles.signedWordProduct profile left)) =
        (NonNullProportion.rotationMatrix (RotationProfiles.signedWordProduct profile right))
      ↔
    NonNullProportion.Equivalent
      (RotationProfiles.signedWordProduct profile left)
      (RotationProfiles.signedWordProduct profile right) :=
  NonNullProportion.rotationMatrix_eq_iff_equivalent _ _ (by decide)

set_option genInjectivity false in
/-- A retained member of the exact finite `chi` image locating one supplied word. -/
structure LocatedClass
    {rotations : List (Rotations.Basic.Rotation
      Scalar)}
    (profile : RotationProfiles.VisibleRotationProfile rotations)
    (word : Word profile) where
  /-- The retained finite-image entry locating this word. -/ entry : Boolean.Basic.Entry profile.targetProfile.vectors
  /-- The retained entry belongs to the original profile's exact finite image. -/ member : entry ∈
    profile.targetProfile.span.entries
  /-- The word's XOR signature is exactly the retained entry vector. -/ vector_eq : RotationProfiles.signedWordVector
    profile word =
    entry.vector

constructive_injectivity LocatedClass

/-- Executably locate the unique displayed image vector of one finite word. The search itself is finite; the impossible
branch is discharged by the span completeness certificate. -/
def locateClass
    {rotations : List (Rotations.Basic.Rotation
      Scalar)}
    (profile : RotationProfiles.VisibleRotationProfile rotations)
    (word : Word profile) :
      LocatedClass profile word := by
  let target := RotationProfiles.signedWordVector profile word
  match searchResult : Search.search target
      profile.targetProfile.span.entries with
  | LinearAlgebra.Span.Boolean.Search.found entry member vectorEq =>
      exact ⟨entry, member, vectorEq.symm⟩
  | LinearAlgebra.Span.Boolean.Search.absent notFound =>
      have impossible : False := by
        rcases RotationProfiles.classifySignedWord profile word with
          ⟨entry, member, vectorEq⟩
        exact notFound entry member vectorEq.symm
      exact False.elim impossible

set_option genInjectivity false in
/-- Cached result of one arbitrary finite-word query. -/
structure WordEvaluation
    {rotations : List (Rotations.Basic.Rotation
      Scalar)}
    (profile : RotationProfiles.VisibleRotationProfile rotations)
    (word : Word profile) where
  /-- The cached evaluated quaternion product of the supplied word. -/ proportion : Projective.Basic.NonNullProportion
    Scalar
  /-- The cached proportion is exactly the finite signed-word product. -/ proportion_eq : proportion =
    RotationProfiles.signedWordProduct profile word
  /-- The cached certified rotation represented by the cached proportion. -/ rotation : Rotations.Basic.Rotation
    Scalar
  /-- The cached rotation is the displayed action of the cached proportion. -/ rotation_eq : rotation =
    (NonNullProportion.rotation proportion)
  /-- The cached rational rotation matrix. -/ matrix : Coordinates3.Matrix3
    Scalar
  /-- The cached matrix is exactly the action matrix of the cached proportion. -/ matrix_eq : matrix =
    (NonNullProportion.rotationMatrix proportion)
  /-- The cached positive norm target of the evaluated proportion. -/ target : GeneratorProfiles.Target
  /-- The retained target is exactly the cached proportion's positive norm target. -/ target_eq : target =
    RotationProfiles.proportionTarget proportion
  /-- The cached finite prime signature of the retained target. -/ signature : Signature target
  /-- The signature is exactly the canonical finite computation for the retained target. -/ signature_eq : signature =
    compute target
  /-- The cached Boolean signature on the profile's original finite support. -/ vector : Data.Vector.Boolean
    profile.targetProfile.finiteSupport.length
  /-- The cached vector is exactly the XOR evaluation of the supplied word. -/ vector_eq : vector =
    RotationProfiles.signedWordVector profile word
  /-- The retained exact finite-image location of the original word. -/ located :
    LocatedClass profile word
  /-- The retained kernel normalization of the cached proportion. -/ normalization :
    KernelNormalization proportion

constructive_injectivity WordEvaluation

/-- Evaluate and retain all expensive finite data for one word exactly once. -/
def evaluate
    {rotations : List (Rotations.Basic.Rotation
      Scalar)}
    (profile : RotationProfiles.VisibleRotationProfile rotations)
    (word : Word profile) :
      WordEvaluation profile word := by
  let proportion := RotationProfiles.signedWordProduct profile word
  let target := RotationProfiles.proportionTarget proportion
  exact
    { proportion := proportion
      proportion_eq := rfl
      rotation := (NonNullProportion.rotation proportion)
      rotation_eq := rfl
      matrix := (NonNullProportion.rotationMatrix proportion)
      matrix_eq := rfl
      target := target
      target_eq := rfl
      signature := compute target
      signature_eq := rfl
      vector := RotationProfiles.signedWordVector profile word
      vector_eq := rfl
      located := locateClass profile word
      normalization := kernelNormalization
        proportion }

end Classification.GeneratedSubgroups

set_option genInjectivity false in
/-- The complete finite quotient statement for a supplied generator list. There are exactly `2^rank` visible kernel
cosets; every finite word has one, every retained class has a realizing word, and kernel and coset equality are the
exact zero/equality tests above. -/
structure Classification (rotations : List (Rotations.Basic.Rotation
  Geometry.Rotations.Rational.Generators.Classification.GeneratedSubgroups.Scalar)) where
  /-- The retained finite rotation profile of the supplied generators. -/ profile :
    RotationProfiles.VisibleRotationProfile rotations
  /-- The retained profile is exactly the canonical profile computed from the supplied generator list. -/ profile_eq :
    profile =
    RotationProfiles.visibleRotationProfile rotations
  /-- The retained finite image contains no duplicate signature vectors. -/ image_nodup :
    (profile.targetProfile.span.entries.map
      Entry.vector).Nodup
  /-- The retained finite image has exactly two to the retained Boolean rank entries. -/ image_cardinality :
    profile.targetProfile.span.entries.length =
    2 ^ profile.targetProfile.span.rank
  /-- Compute a certified cached evaluation for each supplied finite signed word. -/ evaluate_word : ∀ word :
    Geometry.Rotations.Rational.Generators.Classification.GeneratedSubgroups.Word profile,
    Geometry.Rotations.Rational.Generators.Classification.GeneratedSubgroups.WordEvaluation profile word
  /-- Decide exact rotation equality for each supplied pair of finite signed words. -/ compare_words : ∀ left right :
    Geometry.Rotations.Rational.Generators.Classification.GeneratedSubgroups.Word profile,
    Geometry.Rotations.Rational.Generators.Classification.GeneratedSubgroups.ElementComparison profile left right
  /-- Equal word matrices are exactly projectively equivalent evaluated quaternion representatives. -/ equality_exact :
    ∀ left right : Geometry.Rotations.Rational.Generators.Classification.GeneratedSubgroups.Word profile,
    (NonNullProportion.rotationMatrix (RotationProfiles.signedWordProduct profile left)) =
        (NonNullProportion.rotationMatrix (RotationProfiles.signedWordProduct profile right))
      ↔
    NonNullProportion.Equivalent
      (RotationProfiles.signedWordProduct profile left)
      (RotationProfiles.signedWordProduct profile right)
  /-- Finite-word concatenation evaluates to quaternion multiplication. -/ product_exact : ∀ left right :
    Geometry.Rotations.Rational.Generators.Classification.GeneratedSubgroups.Word profile,
    RotationProfiles.signedWordProduct profile (left ++ right) =
      NonNullProportion.mul
        (RotationProfiles.signedWordProduct profile left)
        (RotationProfiles.signedWordProduct profile right)
  /-- Reversing and toggling a finite word evaluates to quaternion conjugation. -/ inverse_exact : ∀ word :
    Geometry.Rotations.Rational.Generators.Classification.GeneratedSubgroups.Word profile,
    RotationProfiles.signedWordProduct profile
      (Geometry.Rotations.Rational.Generators.Classification.GeneratedSubgroups.inverseWord word) =
      NonNullProportion.conjugate
        (RotationProfiles.signedWordProduct profile word)
  /-- Concatenation adds the retained parity signatures by XOR. -/ chi_product : ∀ left right :
    Geometry.Rotations.Rational.Generators.Classification.GeneratedSubgroups.Word profile,
    RotationProfiles.signedWordVector profile (left ++ right) =
      Boolean.Basic.xor
        (RotationProfiles.signedWordVector profile left)
        (RotationProfiles.signedWordVector profile right)
  /-- Word inversion preserves the retained parity signature. -/ chi_inverse : ∀ word :
    Geometry.Rotations.Rational.Generators.Classification.GeneratedSubgroups.Word profile,
    RotationProfiles.signedWordVector profile
      (Geometry.Rotations.Rational.Generators.Classification.GeneratedSubgroups.inverseWord word) =
      RotationProfiles.signedWordVector profile word
  /-- Every finite word has a representative in the retained exact finite image. -/ word_classification : ∀ word :
    Geometry.Rotations.Rational.Generators.Classification.GeneratedSubgroups.Word profile,
    ∃ entry ∈ profile.targetProfile.span.entries,
      RotationProfiles.signedWordVector profile word = entry.vector
  /-- Every retained image entry has the supplied finite selection word realizing its signature. -/ image_realization :
    ∀ entry ∈ profile.targetProfile.span.entries,
    GeneratorProfiles.signatureVector
        profile.targetProfile.finiteSupport
        (RotationProfiles.proportionTarget
          (RotationProfiles.signedSelectionProduct profile
            (RotationProfiles.entrySignedWord profile entry))) =
      entry.vector
  /-- A finite word has a unit representative exactly when its complete parity signature is zero. -/ kernel_exact : ∀
    word : Geometry.Rotations.Rational.Generators.Classification.GeneratedSubgroups.Word profile,
    QuaternionObstruction.HasUnitRepresentative
        (RotationProfiles.signedWordProduct profile word) ↔
      RotationProfiles.signedWordVector profile word =
        Boolean.Basic.zero
          profile.targetProfile.finiteSupport.length
  /-- Two finite words lie in the same unit-kernel coset exactly when their complete parity signatures agree. -/
    cosets_exact : ∀ left right : Geometry.Rotations.Rational.Generators.Classification.GeneratedSubgroups.Word profile,
    NonNullProportion.InSameUnitKernelCoset
        (RotationProfiles.signedWordProduct profile left)
        (RotationProfiles.signedWordProduct profile right) ↔
      RotationProfiles.signedWordVector profile left =
        RotationProfiles.signedWordVector profile right

constructive_injectivity Classification

namespace Classification.GeneratedSubgroups

/-- Problem 70's finitely generated subgroup classification, interpreted entirely through arbitrary finite signed-word
queries and the exact finite `chi` quotient. -/
def classify (rotations : List (Rotations.Basic.Rotation
  Scalar)) :
  Classification rotations := by
  let profile := RotationProfiles.visibleRotationProfile rotations
  exact
    { profile := profile
      profile_eq := rfl
      image_nodup := profile.targetProfile.span.vectors_nodup
      image_cardinality := profile.targetProfile.span.length_eq
      evaluate_word := evaluate profile
      compare_words := compareElements profile
      equality_exact :=
        signedWords_sameRotation_iff_equivalent
        profile
      product_exact := signedWordProduct_append
        profile
      inverse_exact :=
        signedWordProduct_inverseWord profile
      chi_product := signedWordVector_append
        profile
      chi_inverse :=
        signedWordVector_inverseWord profile
      word_classification :=
        RotationProfiles.classifySignedWord profile
      image_realization := fun entry _member =>
        RotationProfiles.entrySignedWord_realizes profile entry
      kernel_exact :=

          signedWord_hasUnitRepresentative_iff_vector_zero
          profile
      cosets_exact :=
        signedWords_sameKernelCoset_iff_vector_eq
        profile }

end Classification.GeneratedSubgroups

end _root_.Purelib.Geometry.Rotations.Rational.Generators.Classification.GeneratedSubgroups

end Purelib.Geometry.Rotations.Rational.Generators
