import RationalRotations.FiniteRotationProfiles
import RationalRotations.QuaternionObstruction

/-!
# Finite-query classification of finitely generated rational rotation groups

Problem 70 asks for the finitely generated subgroups visible through the
quadrance-class map.  This module gives the strongest finite-only reading of
that request.  A supplied finite generator list determines finite signed
words, exact quaternion and rotation-matrix evaluation, an exact finite
`chi`-image, and exact kernel-coset tests.  It deliberately never forms the
set of all words, a completed generated subgroup, or an infinite quotient.
-/

namespace RationalRotations

namespace FiniteGeneratedSubgroups

open PositiveSquareClassSignatures

abbrev Scalar := FiniteRotationProfiles.Scalar

abbrev Word {rotations : List (Rotation Scalar)}
    (profile : FiniteRotationProfiles.VisibleRotationProfile rotations) :=
  List (FiniteRotationProfiles.SignedLetter profile)

private theorem identityProportion_eq_identity
    (witness : NonNullProportion Scalar) :
    FiniteRotationProfiles.identityProportion =
      NonNullProportion.identity witness := by
  apply NonNullProportion.ext (K := Scalar) <;> rfl

@[simp] theorem identityProportion_mul
    (proportion : NonNullProportion Scalar) :
    NonNullProportion.mul FiniteRotationProfiles.identityProportion
      proportion = proportion := by
  rw [identityProportion_eq_identity proportion,
    NonNullProportion.identity_mul]

@[simp] theorem mul_identityProportion
    (proportion : NonNullProportion Scalar) :
    NonNullProportion.mul proportion
      FiniteRotationProfiles.identityProportion = proportion := by
  rw [identityProportion_eq_identity proportion,
    NonNullProportion.mul_identity]

/-- Concatenation is the finite-word multiplication operation. -/
theorem signedWordProduct_append
    {rotations : List (Rotation Scalar)}
    (profile : FiniteRotationProfiles.VisibleRotationProfile rotations) :
    ∀ left right : Word profile,
      FiniteRotationProfiles.signedWordProduct profile (left ++ right) =
        NonNullProportion.mul
          (FiniteRotationProfiles.signedWordProduct profile left)
          (FiniteRotationProfiles.signedWordProduct profile right)
  | [], right => by
      change FiniteRotationProfiles.signedWordProduct profile right =
        NonNullProportion.mul FiniteRotationProfiles.identityProportion
          (FiniteRotationProfiles.signedWordProduct profile right)
      rw [identityProportion_mul]
  | letter :: tail, right => by
      change NonNullProportion.mul
          (FiniteRotationProfiles.selectedProportion letter)
          (FiniteRotationProfiles.signedWordProduct profile (tail ++ right)) =
        NonNullProportion.mul
          (NonNullProportion.mul
            (FiniteRotationProfiles.selectedProportion letter)
            (FiniteRotationProfiles.signedWordProduct profile tail))
          (FiniteRotationProfiles.signedWordProduct profile right)
      rw [signedWordProduct_append profile tail right]
      exact (NonNullProportion.mul_assoc
        (FiniteRotationProfiles.selectedProportion letter)
        (FiniteRotationProfiles.signedWordProduct profile tail)
        (FiniteRotationProfiles.signedWordProduct profile right)).symm

/-- The finite `chi` evaluator sends word concatenation to vector XOR. -/
theorem signedWordVector_append
    {rotations : List (Rotation Scalar)}
    (profile : FiniteRotationProfiles.VisibleRotationProfile rotations) :
    ∀ left right : Word profile,
      FiniteRotationProfiles.signedWordVector profile (left ++ right) =
        RFAP.FiniteBooleanSpan.xor
          (FiniteRotationProfiles.signedWordVector profile left)
          (FiniteRotationProfiles.signedWordVector profile right)
  | [], right => by
      change FiniteRotationProfiles.signedWordVector profile right =
        RFAP.FiniteBooleanSpan.xor
          (RFAP.FiniteBooleanSpan.zero
            profile.targetProfile.finiteSupport.length)
          (FiniteRotationProfiles.signedWordVector profile right)
      exact (RFAP.FiniteBooleanSpan.zero_xor _).symm
  | letter :: tail, right => by
      change RFAP.FiniteBooleanSpan.xor
          (FiniteGeneratorProfiles.signatureVector
            profile.targetProfile.finiteSupport letter.generator.target)
          (FiniteRotationProfiles.signedWordVector profile (tail ++ right)) =
        RFAP.FiniteBooleanSpan.xor
          (RFAP.FiniteBooleanSpan.xor
            (FiniteGeneratorProfiles.signatureVector
              profile.targetProfile.finiteSupport letter.generator.target)
            (FiniteRotationProfiles.signedWordVector profile tail))
          (FiniteRotationProfiles.signedWordVector profile right)
      rw [signedWordVector_append profile tail right]
      exact (RFAP.FiniteBooleanSpan.xor_assoc _ _ _).symm

/-- Toggle one displayed generator occurrence between the forward and inverse
directions. -/
def inverseLetter {rotations : List (Rotation Scalar)}
    {profile : FiniteRotationProfiles.VisibleRotationProfile rotations}
    (letter : FiniteRotationProfiles.SignedLetter profile) :
    FiniteRotationProfiles.SignedLetter profile where
  generator := letter.generator
  member := letter.member
  inverse := !letter.inverse

theorem selectedProportion_inverseLetter
    {rotations : List (Rotation Scalar)}
    {profile : FiniteRotationProfiles.VisibleRotationProfile rotations}
    (letter : FiniteRotationProfiles.SignedLetter profile) :
    FiniteRotationProfiles.selectedProportion (inverseLetter letter) =
      NonNullProportion.conjugate
        (FiniteRotationProfiles.selectedProportion letter) := by
  cases letter with
  | mk generator member inverse =>
      cases inverse with
      | false => rfl
      | true =>
          exact (NonNullProportion.conjugate_conjugate
            generator.proportion).symm

/-- Reverse a finite signed word and toggle every sign. -/
def inverseWord {rotations : List (Rotation Scalar)}
    {profile : FiniteRotationProfiles.VisibleRotationProfile rotations} :
    Word profile → Word profile
  | [] => []
  | letter :: tail => inverseWord tail ++ [inverseLetter letter]

/-- The explicit inverse-word algorithm evaluates to quaternion
conjugation. -/
theorem signedWordProduct_inverseWord
    {rotations : List (Rotation Scalar)}
    (profile : FiniteRotationProfiles.VisibleRotationProfile rotations) :
    ∀ word : Word profile,
      FiniteRotationProfiles.signedWordProduct profile (inverseWord word) =
        NonNullProportion.conjugate
          (FiniteRotationProfiles.signedWordProduct profile word)
  | [] => by
      apply NonNullProportion.ext (K := Scalar) <;> rfl
  | letter :: tail => by
      change FiniteRotationProfiles.signedWordProduct profile
          (inverseWord tail ++ [inverseLetter letter]) =
        NonNullProportion.conjugate
          (NonNullProportion.mul
            (FiniteRotationProfiles.selectedProportion letter)
            (FiniteRotationProfiles.signedWordProduct profile tail))
      rw [signedWordProduct_append, signedWordProduct_inverseWord,
        show FiniteRotationProfiles.signedWordProduct profile
            [inverseLetter letter] =
          NonNullProportion.conjugate
            (FiniteRotationProfiles.selectedProportion letter) by
          change NonNullProportion.mul
              (FiniteRotationProfiles.selectedProportion
                (inverseLetter letter))
              FiniteRotationProfiles.identityProportion = _
          rw [mul_identityProportion, selectedProportion_inverseLetter],
        NonNullProportion.conjugate_mul_reverse]

/-- Inversion fixes the `chi` vector because every rational square class has
order at most two. -/
theorem signedWordVector_inverseWord
    {rotations : List (Rotation Scalar)}
    (profile : FiniteRotationProfiles.VisibleRotationProfile rotations) :
    ∀ word : Word profile,
      FiniteRotationProfiles.signedWordVector profile (inverseWord word) =
        FiniteRotationProfiles.signedWordVector profile word
  | [] => rfl
  | letter :: tail => by
      rw [inverseWord, signedWordVector_append,
        signedWordVector_inverseWord]
      change RFAP.FiniteBooleanSpan.xor
          (FiniteRotationProfiles.signedWordVector profile tail)
          (RFAP.FiniteBooleanSpan.xor
            (FiniteGeneratorProfiles.signatureVector
              profile.targetProfile.finiteSupport letter.generator.target)
            (RFAP.FiniteBooleanSpan.zero
              profile.targetProfile.finiteSupport.length)) =
        RFAP.FiniteBooleanSpan.xor
          (FiniteGeneratorProfiles.signatureVector
            profile.targetProfile.finiteSupport letter.generator.target)
          (FiniteRotationProfiles.signedWordVector profile tail)
      rw [RFAP.FiniteBooleanSpan.xor_zero,
        RFAP.FiniteBooleanSpan.xor_comm]

/-- Every prime in the computed norm signature of a finite word already lies
in the cached union of the generator supports. -/
theorem signedWordTarget_primes_subset
    {rotations : List (Rotation Scalar)}
    (profile : FiniteRotationProfiles.VisibleRotationProfile rotations) :
    ∀ (word : Word profile) (prime : Nat),
      prime ∈ (compute
        (FiniteRotationProfiles.signedWordTarget profile word)).primes →
      prime ∈ profile.targetProfile.finiteSupport
  | [], prime, member => by
      change prime ∈ (compute
        (FiniteRotationProfiles.proportionTarget
          FiniteRotationProfiles.identityProportion)).primes at member
      rw [FiniteRotationProfiles.identity_target_primes_empty] at member
      nomatch member
  | letter :: tail, prime, member => by
      have productSupport := compute_mulTarget_support
        letter.generator.target
        (FiniteRotationProfiles.signedWordTarget profile tail) prime
      have xorMember := productSupport.mp member
      rcases (mem_xorSupport_iff prime _ _).mp xorMember with
        generatorOnly | tailOnly
      · rw [profile.targetProfile.finiteSupport_eq]
        apply FiniteGeneratorProfiles.target_primes_subset_support
          (target := letter.generator.target)
        · apply QuotientFreeList.mem_map.mpr
          exact ⟨letter.generator, letter.member, rfl⟩
        · exact generatorOnly.1
      · exact signedWordTarget_primes_subset profile tail prime tailOnly.1

private theorem natContains_eq_of_signatureBits_eq
    (prime : Nat) : ∀ (finiteSupport leftPrimes rightPrimes : List Nat),
    prime ∈ finiteSupport →
      FiniteGeneratorProfiles.signatureBits finiteSupport leftPrimes =
        FiniteGeneratorProfiles.signatureBits finiteSupport rightPrimes →
      natContains prime leftPrimes = natContains prime rightPrimes
  | [], _leftPrimes, _rightPrimes, impossible, _equal => by
      nomatch impossible
  | head :: tail, leftPrimes, rightPrimes, member, equal => by
      simp only [FiniteGeneratorProfiles.signatureBits, List.map_cons,
        List.cons.injEq] at equal
      rcases List.mem_cons.mp member with headEq | tailMember
      · exact headEq ▸ equal.1
      · exact natContains_eq_of_signatureBits_eq prime tail leftPrimes
          rightPrimes tailMember equal.2

private theorem signatureBits_eq_of_same_members
    (finiteSupport leftPrimes rightPrimes : List Nat)
    (sameMembers : ∀ prime, prime ∈ leftPrimes ↔ prime ∈ rightPrimes) :
    FiniteGeneratorProfiles.signatureBits finiteSupport leftPrimes =
      FiniteGeneratorProfiles.signatureBits finiteSupport rightPrimes := by
  induction finiteSupport with
  | nil => rfl
  | cons prime tail inductionHypothesis =>
      simp only [FiniteGeneratorProfiles.signatureBits, List.map_cons,
        List.cons.injEq]
      constructor
      · cases leftContains : natContains prime leftPrimes <;>
          cases rightContains : natContains prime rightPrimes
        · rfl
        · have leftAbsent :=
            (natContains_eq_false_iff prime leftPrimes).mp leftContains
          have rightMember :=
            (natContains_eq_true_iff prime rightPrimes).mp rightContains
          exact False.elim (leftAbsent ((sameMembers prime).mpr rightMember))
        · have leftMember :=
            (natContains_eq_true_iff prime leftPrimes).mp leftContains
          have rightAbsent :=
            (natContains_eq_false_iff prime rightPrimes).mp rightContains
          exact False.elim (rightAbsent ((sameMembers prime).mp leftMember))
        · rfl
      · exact inductionHypothesis

private theorem signatureBits_empty (finiteSupport : List Nat) :
    FiniteGeneratorProfiles.signatureBits finiteSupport [] =
      List.replicate finiteSupport.length false := by
  induction finiteSupport with
  | nil => rfl
  | cons _prime tail inductionHypothesis =>
      simp only [FiniteGeneratorProfiles.signatureBits, List.map_cons,
        natContains, List.length_cons, List.replicate_succ,
        List.cons.injEq, true_and]
      exact inductionHypothesis

private theorem signatureVector_eq_zero_iff_primes_empty_of_subset
    (finiteSupport : List Nat)
    (target : FiniteGeneratorProfiles.Target)
    (subset : ∀ prime, prime ∈ (compute target).primes →
      prime ∈ finiteSupport) :
    FiniteGeneratorProfiles.signatureVector finiteSupport target =
        RFAP.FiniteBooleanSpan.zero finiteSupport.length ↔
      (compute target).primes = [] := by
  constructor
  · intro vectorZero
    have bitsZero := congrArg RFAP.FiniteBooleanSpan.Vector.bits vectorZero
    change FiniteGeneratorProfiles.signatureBits finiteSupport
        (compute target).primes = List.replicate finiteSupport.length false
      at bitsZero
    cases primesEq : (compute target).primes with
    | nil => rfl
    | cons prime tail =>
        have member : prime ∈ (compute target).primes := by
          rw [primesEq]
          exact List.mem_cons_self
        have supportMember := subset prime member
        have zeroBits :
            FiniteGeneratorProfiles.signatureBits finiteSupport
                (compute target).primes =
              FiniteGeneratorProfiles.signatureBits finiteSupport [] :=
          bitsZero.trans (signatureBits_empty finiteSupport).symm
        have containsFalse :
            natContains prime (compute target).primes = false := by
          have containsEqual := natContains_eq_of_signatureBits_eq prime
            finiteSupport (compute target).primes [] supportMember zeroBits
          simpa only [natContains] using containsEqual
        have notMember :=
          (natContains_eq_false_iff prime (compute target).primes).mp
            containsFalse
        exact False.elim (notMember member)
  · intro primesEmpty
    apply RFAP.FiniteBooleanSpan.Vector.ext
    change FiniteGeneratorProfiles.signatureBits finiteSupport
        (compute target).primes = List.replicate finiteSupport.length false
    rw [primesEmpty]
    exact signatureBits_empty finiteSupport

/-- On a support containing both complete finite signatures, equality of
Boolean vectors is exactly rational square-class equivalence. -/
theorem signatureVector_eq_iff_equivalent_of_subsets
    (finiteSupport : List Nat)
    (left right : FiniteGeneratorProfiles.Target)
    (leftSubset : ∀ prime, prime ∈ (compute left).primes →
      prime ∈ finiteSupport)
    (rightSubset : ∀ prime, prime ∈ (compute right).primes →
      prime ∈ finiteSupport) :
    FiniteGeneratorProfiles.signatureVector finiteSupport left =
        FiniteGeneratorProfiles.signatureVector finiteSupport right ↔
      left.representative.Equivalent right.representative := by
  let leftSignature := compute left
  let rightSignature := compute right
  constructor
  · intro vectorEqual
    have bitsEqual := congrArg RFAP.FiniteBooleanSpan.Vector.bits vectorEqual
    change FiniteGeneratorProfiles.signatureBits finiteSupport
        leftSignature.primes =
      FiniteGeneratorProfiles.signatureBits finiteSupport
        rightSignature.primes at bitsEqual
    have sameMembers : ∀ prime,
        prime ∈ leftSignature.primes ↔ prime ∈ rightSignature.primes := by
      intro prime
      constructor
      · intro leftMember
        have supportMember := leftSubset prime leftMember
        have containsEqual := natContains_eq_of_signatureBits_eq prime
          finiteSupport leftSignature.primes rightSignature.primes
          supportMember bitsEqual
        have leftTrue :=
          (natContains_eq_true_iff prime leftSignature.primes).mpr leftMember
        apply (natContains_eq_true_iff prime rightSignature.primes).mp
        rw [← containsEqual]
        exact leftTrue
      · intro rightMember
        have supportMember := rightSubset prime rightMember
        have containsEqual := natContains_eq_of_signatureBits_eq prime
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
          (by simpa only [leftSignature.kernel_eq] using
            leftSignature.kernel_positive)).Equivalent
        (positiveNaturalClass rightSignature.primes.prod
          (by simpa only [rightSignature.kernel_eq] using
            rightSignature.kernel_positive)) := by
      simpa only [leftSignature.kernel_eq, rightSignature.kernel_eq] using
        kernelEquivalent
    have sameMembers := (primeSupportEquivalent_iff
      leftSignature.primes_prime rightSignature.primes_prime
      leftSignature.primes_nodup rightSignature.primes_nodup).mp
        displayedEquivalent
    apply RFAP.FiniteBooleanSpan.Vector.ext
    exact signatureBits_eq_of_same_members finiteSupport
      leftSignature.primes rightSignature.primes sameMembers

/-- Cached normalizer for one rational projective proportion.  Scaling by
this explicit inverse square factor changes its norm to the computed natural
kernel, whether or not that kernel is one. -/
structure KernelNormalization (proportion : NonNullProportion Scalar) where
  signature : Signature
    (FiniteRotationProfiles.proportionTarget proportion)
  signature_eq : signature = compute
    (FiniteRotationProfiles.proportionTarget proportion)
  factor : Scalar
  factor_eq : factor = signature.squareFactor⁻¹
  factorNonzero : factor ≠ 0
  norm_eq_kernel :
    (Proportion.scale factor proportion.toProportion).norm =
      (signature.kernel : Scalar)

/-- Compute and retain the finite square-class normalizer. -/
def kernelNormalization (proportion : NonNullProportion Scalar) :
    KernelNormalization proportion := by
  let signature := compute
    (FiniteRotationProfiles.proportionTarget proportion)
  let factor := signature.squareFactor⁻¹
  have factorNonzero : factor ≠ 0 :=
    RFAP.ExplicitField.inv_ne_zero signature.squareFactor_nonzero
  refine
    { signature := signature
      signature_eq := rfl
      factor := factor
      factor_eq := rfl
      factorNonzero := factorNonzero
      norm_eq_kernel := ?_ }
  rw [Proportion.norm_scale]
  change factor ^ 2 *
      (FiniteRotationProfiles.proportionTarget proportion).representative.value =
    (signature.kernel : Scalar)
  rw [signature.value_eq_squareFactor_sq_mul_kernel]
  have cancel := RFAP.ExplicitField.mul_inv_cancel signature.squareFactor
    signature.squareFactor_nonzero
  unfold factor
  calc
    signature.squareFactor⁻¹ ^ 2 *
        (signature.squareFactor ^ 2 * (signature.kernel : Scalar)) =
      (signature.squareFactor * signature.squareFactor⁻¹) ^ 2 *
        (signature.kernel : Scalar) := by ring1
    _ = (signature.kernel : Scalar) := by rw [cancel]; ring1

/-- When the computed kernel is one, the cached normalizer becomes an
executable norm-one representative certificate. -/
def unitRepresentativeCertificateOfKernelEqOne
    (proportion : NonNullProportion Scalar)
    (kernelOne :
      (compute (FiniteRotationProfiles.proportionTarget proportion)).kernel =
        1) :
    NonNullProportion.UnitRepresentativeCertificate proportion := by
  let normalization := kernelNormalization proportion
  refine
    { factor := normalization.factor
      factorNonzero := normalization.factorNonzero
      normOne := ?_ }
  calc
    (Proportion.scale normalization.factor proportion.toProportion).norm =
        (normalization.signature.kernel : Scalar) :=
      normalization.norm_eq_kernel
    _ = (1 : Scalar) := by
      rw [normalization.signature_eq, kernelOne]
      rfl

private def oneTarget : FiniteGeneratorProfiles.Target :=
  positiveNaturalTarget 1 (by decide)

private theorem oneTarget_kernel_eq_one :
    (compute oneTarget).kernel = 1 := by decide +kernel

/-- Over the rationals, kernel membership is decided exactly by the cached
natural odd-prime kernel.  The reverse implication returns the explicit
normalizing scalar above. -/
theorem hasUnitRepresentative_iff_kernel_eq_one
    (proportion : NonNullProportion Scalar) :
    proportion.HasUnitRepresentative ↔
      (compute
        (FiniteRotationProfiles.proportionTarget proportion)).kernel = 1 := by
  constructor
  · intro unit
    have trivialClass :=
      (NonNullProportion.hasUnitRepresentative_iff_quadranceClass_trivial
        proportion).mp unit
    have unitClassEq : proportion.unitSquareClass = oneTarget.representative := by
      apply SquareClassRepresentative.ext
      rfl
    have equivalentOne :
        SquareClassRepresentative.Equivalent
          (FiniteRotationProfiles.proportionTarget proportion).representative
          oneTarget.representative := by
      rw [← unitClassEq]
      exact trivialClass
    have kernelsEqual := (equivalent_iff_kernel_eq
      (compute (FiniteRotationProfiles.proportionTarget proportion))
      (compute oneTarget)).mp equivalentOne
    exact kernelsEqual.trans oneTarget_kernel_eq_one
  · intro kernelOne
    exact NonNullProportion.UnitRepresentativeCertificate.hasUnitRepresentative
      (unitRepresentativeCertificateOfKernelEqOne proportion kernelOne)

/-- A signed word lies in the restricted unit-quaternion kernel exactly when
its complete finite XOR signature is zero. -/
theorem signedWord_hasUnitRepresentative_iff_vector_zero
    {rotations : List (Rotation Scalar)}
    (profile : FiniteRotationProfiles.VisibleRotationProfile rotations)
    (word : Word profile) :
    NonNullProportion.HasUnitRepresentative
        (FiniteRotationProfiles.signedWordProduct profile word) ↔
      FiniteRotationProfiles.signedWordVector profile word =
        RFAP.FiniteBooleanSpan.zero
          profile.targetProfile.finiteSupport.length := by
  rw [hasUnitRepresentative_iff_kernel_eq_one,
    FiniteRotationProfiles.signedWordProduct_target]
  let signature := compute
    (FiniteRotationProfiles.signedWordTarget profile word)
  rw [signature.kernel_eq_one_iff_primes_eq_nil]
  rw [← signatureVector_eq_zero_iff_primes_empty_of_subset
    profile.targetProfile.finiteSupport
    (FiniteRotationProfiles.signedWordTarget profile word)
    (signedWordTarget_primes_subset profile word)]
  rw [FiniteRotationProfiles.signedWordTarget_signature]

/-- Two finite words represent the same coset of the restricted kernel
exactly when their finite `chi` vectors agree. -/
theorem signedWords_sameKernelCoset_iff_vector_eq
    {rotations : List (Rotation Scalar)}
    (profile : FiniteRotationProfiles.VisibleRotationProfile rotations)
    (left right : Word profile) :
    NonNullProportion.InSameUnitKernelCoset
        (FiniteRotationProfiles.signedWordProduct profile left)
        (FiniteRotationProfiles.signedWordProduct profile right) ↔
      FiniteRotationProfiles.signedWordVector profile left =
        FiniteRotationProfiles.signedWordVector profile right := by
  rw [NonNullProportion.inSameUnitKernelCoset_iff_quadranceClass_equivalent]
  change SquareClassRepresentative.Equivalent
      (FiniteRotationProfiles.proportionTarget
        (FiniteRotationProfiles.signedWordProduct profile left)).representative
      (FiniteRotationProfiles.proportionTarget
        (FiniteRotationProfiles.signedWordProduct profile right)).representative
      ↔ _
  rw [FiniteRotationProfiles.signedWordProduct_target,
    FiniteRotationProfiles.signedWordProduct_target]
  rw [← signatureVector_eq_iff_equivalent_of_subsets
    profile.targetProfile.finiteSupport
    (FiniteRotationProfiles.signedWordTarget profile left)
    (FiniteRotationProfiles.signedWordTarget profile right)
    (signedWordTarget_primes_subset profile left)
    (signedWordTarget_primes_subset profile right)]
  rw [FiniteRotationProfiles.signedWordTarget_signature,
    FiniteRotationProfiles.signedWordTarget_signature]

/-- Exact finite comparison of two word evaluations as rotations. -/
inductive ElementComparison
    {rotations : List (Rotation Scalar)}
    (profile : FiniteRotationProfiles.VisibleRotationProfile rotations)
    (left right : Word profile) : Type
  | same (matrix_eq :
      (FiniteRotationProfiles.signedWordProduct profile left).rotationMatrix =
        (FiniteRotationProfiles.signedWordProduct profile right).rotationMatrix)
  | different (matrix_ne :
      (FiniteRotationProfiles.signedWordProduct profile left).rotationMatrix ≠
        (FiniteRotationProfiles.signedWordProduct profile right).rotationMatrix)

/-- Compare all nine rational matrix entries; no enumeration of other words
is involved. -/
def compareElements
    {rotations : List (Rotation Scalar)}
    (profile : FiniteRotationProfiles.VisibleRotationProfile rotations)
    (left right : Word profile) : ElementComparison profile left right :=
  if equal :
      (FiniteRotationProfiles.signedWordProduct profile left).rotationMatrix =
        (FiniteRotationProfiles.signedWordProduct profile right).rotationMatrix
  then ElementComparison.same equal
  else ElementComparison.different equal

/-- Exact matrix equality is also exactly projective equality of the two
evaluated quaternion products. -/
theorem signedWords_sameRotation_iff_equivalent
    {rotations : List (Rotation Scalar)}
    (profile : FiniteRotationProfiles.VisibleRotationProfile rotations)
    (left right : Word profile) :
    (FiniteRotationProfiles.signedWordProduct profile left).rotationMatrix =
        (FiniteRotationProfiles.signedWordProduct profile right).rotationMatrix
      ↔
    NonNullProportion.Equivalent
      (FiniteRotationProfiles.signedWordProduct profile left)
      (FiniteRotationProfiles.signedWordProduct profile right) :=
  NonNullProportion.rotationMatrix_eq_iff_equivalent _ _ (by decide)

/-- A retained member of the exact finite `chi` image locating one supplied
word. -/
structure LocatedClass
    {rotations : List (Rotation Scalar)}
    (profile : FiniteRotationProfiles.VisibleRotationProfile rotations)
    (word : Word profile) where
  entry : RFAP.FiniteBooleanSpan.Entry profile.targetProfile.vectors
  member : entry ∈ profile.targetProfile.span.entries
  vector_eq : FiniteRotationProfiles.signedWordVector profile word =
    entry.vector

/-- Executably locate the unique displayed image vector of one finite word.
The search itself is finite; the impossible branch is discharged by the
span completeness certificate. -/
def locateClass
    {rotations : List (Rotation Scalar)}
    (profile : FiniteRotationProfiles.VisibleRotationProfile rotations)
    (word : Word profile) : LocatedClass profile word := by
  let target := FiniteRotationProfiles.signedWordVector profile word
  match searchResult : RFAP.FiniteBooleanSpan.search target
      profile.targetProfile.span.entries with
  | RFAP.FiniteBooleanSpan.Search.found entry member vectorEq =>
      exact ⟨entry, member, vectorEq.symm⟩
  | RFAP.FiniteBooleanSpan.Search.absent notFound =>
      have impossible : False := by
        rcases FiniteRotationProfiles.classifySignedWord profile word with
          ⟨entry, member, vectorEq⟩
        exact notFound entry member vectorEq.symm
      exact False.elim impossible

/-- Cached result of one arbitrary finite-word query. -/
structure WordEvaluation
    {rotations : List (Rotation Scalar)}
    (profile : FiniteRotationProfiles.VisibleRotationProfile rotations)
    (word : Word profile) where
  proportion : NonNullProportion Scalar
  proportion_eq : proportion =
    FiniteRotationProfiles.signedWordProduct profile word
  rotation : Rotation Scalar
  rotation_eq : rotation = proportion.rotation
  matrix : Matrix3 Scalar
  matrix_eq : matrix = proportion.rotationMatrix
  target : FiniteGeneratorProfiles.Target
  target_eq : target = FiniteRotationProfiles.proportionTarget proportion
  signature : Signature target
  signature_eq : signature = compute target
  vector : RFAP.FiniteBooleanSpan.Vector
    profile.targetProfile.finiteSupport.length
  vector_eq : vector = FiniteRotationProfiles.signedWordVector profile word
  located : LocatedClass profile word
  normalization : KernelNormalization proportion

/-- Evaluate and retain all expensive finite data for one word exactly once. -/
def evaluate
    {rotations : List (Rotation Scalar)}
    (profile : FiniteRotationProfiles.VisibleRotationProfile rotations)
    (word : Word profile) : WordEvaluation profile word := by
  let proportion := FiniteRotationProfiles.signedWordProduct profile word
  let target := FiniteRotationProfiles.proportionTarget proportion
  exact
    { proportion := proportion
      proportion_eq := rfl
      rotation := proportion.rotation
      rotation_eq := rfl
      matrix := proportion.rotationMatrix
      matrix_eq := rfl
      target := target
      target_eq := rfl
      signature := compute target
      signature_eq := rfl
      vector := FiniteRotationProfiles.signedWordVector profile word
      vector_eq := rfl
      located := locateClass profile word
      normalization := kernelNormalization proportion }

/-- The complete finite quotient statement for a supplied generator list.
There are exactly `2^rank` visible kernel cosets; every finite word has one,
every retained class has a realizing word, and kernel and coset equality are
the exact zero/equality tests above. -/
structure Classification (rotations : List (Rotation Scalar)) where
  profile : FiniteRotationProfiles.VisibleRotationProfile rotations
  profile_eq : profile =
    FiniteRotationProfiles.visibleRotationProfile rotations
  image_nodup :
    (profile.targetProfile.span.entries.map
      RFAP.FiniteBooleanSpan.Entry.vector).Nodup
  image_cardinality : profile.targetProfile.span.entries.length =
    2 ^ profile.targetProfile.span.rank
  evaluate_word : ∀ word : Word profile, WordEvaluation profile word
  compare_words : ∀ left right : Word profile,
    ElementComparison profile left right
  equality_exact : ∀ left right : Word profile,
    (FiniteRotationProfiles.signedWordProduct profile left).rotationMatrix =
        (FiniteRotationProfiles.signedWordProduct profile right).rotationMatrix
      ↔
    NonNullProportion.Equivalent
      (FiniteRotationProfiles.signedWordProduct profile left)
      (FiniteRotationProfiles.signedWordProduct profile right)
  product_exact : ∀ left right : Word profile,
    FiniteRotationProfiles.signedWordProduct profile (left ++ right) =
      NonNullProportion.mul
        (FiniteRotationProfiles.signedWordProduct profile left)
        (FiniteRotationProfiles.signedWordProduct profile right)
  inverse_exact : ∀ word : Word profile,
    FiniteRotationProfiles.signedWordProduct profile (inverseWord word) =
      NonNullProportion.conjugate
        (FiniteRotationProfiles.signedWordProduct profile word)
  chi_product : ∀ left right : Word profile,
    FiniteRotationProfiles.signedWordVector profile (left ++ right) =
      RFAP.FiniteBooleanSpan.xor
        (FiniteRotationProfiles.signedWordVector profile left)
        (FiniteRotationProfiles.signedWordVector profile right)
  chi_inverse : ∀ word : Word profile,
    FiniteRotationProfiles.signedWordVector profile (inverseWord word) =
      FiniteRotationProfiles.signedWordVector profile word
  word_classification : ∀ word : Word profile,
    ∃ entry ∈ profile.targetProfile.span.entries,
      FiniteRotationProfiles.signedWordVector profile word = entry.vector
  image_realization : ∀ entry ∈ profile.targetProfile.span.entries,
    FiniteGeneratorProfiles.signatureVector
        profile.targetProfile.finiteSupport
        (FiniteRotationProfiles.proportionTarget
          (FiniteRotationProfiles.signedSelectionProduct profile
            (FiniteRotationProfiles.entrySignedWord profile entry))) =
      entry.vector
  kernel_exact : ∀ word : Word profile,
    NonNullProportion.HasUnitRepresentative
        (FiniteRotationProfiles.signedWordProduct profile word) ↔
      FiniteRotationProfiles.signedWordVector profile word =
        RFAP.FiniteBooleanSpan.zero
          profile.targetProfile.finiteSupport.length
  cosets_exact : ∀ left right : Word profile,
    NonNullProportion.InSameUnitKernelCoset
        (FiniteRotationProfiles.signedWordProduct profile left)
        (FiniteRotationProfiles.signedWordProduct profile right) ↔
      FiniteRotationProfiles.signedWordVector profile left =
        FiniteRotationProfiles.signedWordVector profile right

/-- Problem 70's finitely generated subgroup classification, interpreted
entirely through arbitrary finite signed-word queries and the exact finite
`chi` quotient. -/
def classify (rotations : List (Rotation Scalar)) : Classification rotations := by
  let profile := FiniteRotationProfiles.visibleRotationProfile rotations
  exact
    { profile := profile
      profile_eq := rfl
      image_nodup := profile.targetProfile.span.vectors_nodup
      image_cardinality := profile.targetProfile.span.length_eq
      evaluate_word := evaluate profile
      compare_words := compareElements profile
      equality_exact := signedWords_sameRotation_iff_equivalent profile
      product_exact := signedWordProduct_append profile
      inverse_exact := signedWordProduct_inverseWord profile
      chi_product := signedWordVector_append profile
      chi_inverse := signedWordVector_inverseWord profile
      word_classification :=
        FiniteRotationProfiles.classifySignedWord profile
      image_realization := fun entry _member =>
        FiniteRotationProfiles.entrySignedWord_realizes profile entry
      kernel_exact :=
        signedWord_hasUnitRepresentative_iff_vector_zero profile
      cosets_exact := signedWords_sameKernelCoset_iff_vector_eq profile }

end FiniteGeneratedSubgroups

end RationalRotations
